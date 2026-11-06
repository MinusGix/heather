//! The host side of Heather tactics (docs/host-elaboration-interface-design.md).
//!
//! `by t` runs a tactic: an ordinary Heather value of `lib/std/tactic/tactic.hthr`'s
//! `Tac<Expr>`, a tree whose nodes are requests to this elaborator and whose
//! leaves are results. The loop here evaluates the tree to its next node,
//! answers the request against the goal's context, resumes the tree with the
//! answer, and finally turns the `Expr` the tactic returned into a kernel term
//! of the goal type. Nothing the tactic says is trusted: the proof is checked
//! at the goal here and again by the kernel gate with its declaration.
//!
//! The loop is written over [`Speaker`], the protocol from the host's side, so
//! that a tactic implemented in Rust ([`NativeTactic`], design §8a) is driven
//! by exactly the same code as an interpreted Heather one.
//!
//! **Binders.** `Open` introduces a binder's local, so the host answers
//! requests under more than one context. Each context is a [`Scope`]: the
//! goal's is the root, and each opened binder is a child of the scope its
//! function type lived in. Every handle and local belongs to one scope, an
//! `Expr` is elaborated at the deepest scope it mentions, and mixing two
//! scopes neither of which encloses the other is refused: that would use a
//! local outside its binder. Nothing here computes a de Bruijn index from
//! the tactic's say-so; locals are host-issued and positions come from the
//! scope.
//!
//! **Quoting.** While a tactic expression is elaborated, a position that
//! expects a `tactic::Expr` but is given some other term of the goal's
//! context (`by exact(h)`) takes a handle to that term instead
//! ([`Elaborator::quote_for_by`]). The quoted term is replaced by a closed
//! `host_quote(n)`, so the tactic value stays closed.
//!
//! **Holes.** `Hole` makes a metavariable of the run, which the requests that
//! compare terms solve and `Restore` forgets ([`Run`] says how they are
//! represented). Every request zonks before the kernel sees a term, and the
//! result must mention no unsolved hole.
//!
//! **Splits.** `Cases` and `Constructor` split a goal with the elaborator's
//! own `match` or constructor, built from surface syntax whose leaves are
//! markers ([`Leaves`]). The skeleton is elaborated once with every leaf
//! recording its context and statement, which become the branches the tactic
//! proves, and once more by `Close`, with each leaf the branch's proof. So a
//! split's proof is exactly what the same `match` written in source would
//! elaborate to.
//!
//! **Reading the tree.** The host never decodes `Tac`'s lowered encoding by
//! hand. Each question it asks is an application of one of the library's
//! `host_*` functions to the current tree, evaluated to a numeral, an `Expr`
//! or a `String` in the kernel's value domain ([`Reader`], the
//! analyzer path of docs/analyzer-evaluation-design.md), and an answer is
//! built from the library's builders the same way. Each step is a pending
//! application over the previous tree's closure, so nothing is read back into
//! syntax and re-evaluated, and the force cache shares the tree's spine
//! between steps. The one exception is [`Interpreted::pin`], which looks at
//! a resumed tree's outer pair to keep its proof from chaining.

use std::sync::Arc as Rc;

use heather_kernel::level::Level;
use heather_kernel::term::{GlobalBinding, GlobalCtx, GlobalVar, LocalCtx, LocalSubst, LocalVar, Term, Type};
use std::cell::{Cell, RefCell};
use heather_kernel::layer::Layer;
use heather_kernel::subst::{GlobalEntry, GlobalSubst};
use heather_kernel::eval::Eval;
use heather_kernel::reduce::{self, Defs};
use heather_kernel::term::CtxBase;
use heather_kernel::value::{Elim, Env, PiAnn, TmClo, TyClo, Val, ValueArena};
use heather_kernel::value::program::ContextProgram;
use heather_syntax::ast::{Expr, Span};

use crate::oracle::Unfold;
use crate::context::{Alias, Cx};
use crate::unification::Sol;
use crate::{err, Elaborator, R};

/// Fuel for **one force** of the tree's value graph — the kernel's own
/// default, deliberately not a bespoke larger one. Each force runs on the
/// **shared** graph, where the bounded cache avoids recent repeated work, so
/// running out is a decline like any other
/// (docs/analyzer-evaluation-design.md §2).
const READ_FUEL: u64 = heather_kernel::typing::DEFAULT_FUEL;

/// Reads library answers in the kernel's **value domain**: every
/// sub-structure it holds is a [`TmClo`], forced on demand and shared through
/// the arena's cache (docs/analyzer-evaluation-design.md).
pub(crate) struct Reader<'a, 'v> {
    psi: &'a GlobalCtx,
    arena: &'v ValueArena<'v>,
    /// Rescoped definition bodies, memoized for the duration of one read.
    /// Every δ-unfold rescopes the callee's whole body with `shift_global`,
    /// and one query unfolds the same handful of library globals many
    /// times; the cache is owned beside the Ψ it belongs to and dies with the
    /// read, which is the soundness condition `GlobalCache` states for
    /// itself.
    cache: reduce::GlobalCache,
}

impl<'a, 'v> Reader<'a, 'v> {
    pub(crate) fn new(psi: &'a GlobalCtx, arena: &'v ValueArena<'v>) -> Reader<'a, 'v> {
        Reader { psi, arena, cache: reduce::GlobalCache::new() }
    }

    /// A closed term as a sub-structure of the value graph — the root a read
    /// starts from. The empty environment is the identity environment of the
    /// empty Γ, which is the context every application is built at.
    pub(crate) fn root(&self, t: Term) -> &'v TmClo<'v> {
        self.arena.tm(TmClo::syn(Env::empty(), Rc::new(t)))
    }

    /// The δ-transparent weak head **value** of a sub-structure. The arena's
    /// bounded cache shares recent forces while allowing values the walk has
    /// left behind to be reclaimed.
    pub(crate) fn force(&self, c: &'v TmClo<'v>) -> Result<&'v Val<'v>, String> {
        let mut ev = Eval::new(READ_FUEL, Defs::transparent_cached(self.psi, &self.cache), CtxBase::Nil, self.arena);
        ev.force(c).and_then(|v| ev.delta_whnf(v)).map_err(|_| "the host query ran out of fuel".to_string())
    }

    /// A numeral's value, a run of successors at a time. Past a million
    /// single successors it declines (each is a step); a run is read whole,
    /// so a literal word (`0x0123456789abcdef`, which a `runtime fn`'s
    /// reflection quotes back) reads in one step, up to `u64::MAX`.
    pub(crate) fn nat(&self, c: &'v TmClo<'v>) -> Result<u64, String> {
        let mut v = self.force(c)?;
        let mut n = 0u64;
        let mut steps = 0u64;
        loop {
            let next = match &*v {
                Val::Zero => return Ok(n),
                Val::Succ(p) => {
                    n = n.checked_add(1).ok_or("an implausible numeral")?;
                    steps += 1;
                    if steps > 1_000_000 {
                        return Err("an implausible numeral".into());
                    }
                    *p
                }
                Val::NatRun { program, tail } => {
                    let Some(count) = ContextProgram::repetition_count_up_to(program, u64::MAX - n)
                    else {
                        return Err("an implausible numeral".into());
                    };
                    n += count;
                    *tail
                }
                other => return Err(format!("a Nat that is not a numeral: {other:?}")),
            };
            v = self.force(next)?;
        }
    }
}

/// Requests one run may make before it is stopped. A tactic is library code
/// and may loop; fuel bounds each evaluation, this bounds the conversation.
const REQUEST_BUDGET: usize = 10_000;

/// Nodes of one returned `Expr`, and characters of one `String`, the host
/// will read before declining (the runaway discipline: the value is produced
/// by library code and may be arbitrarily large).
const READ_BUDGET: usize = 4096;

/// Leading parameters `Match` will treat as unknowns before giving up.
const MATCH_PARAMETERS: usize = 64;


/// What one `Match` learns about class parameters, shared by its attempts at
/// every parameter count: the goals the dictionaries in scope answer, per
/// class, and resolution's answer per goal.
#[derive(Default)]
struct MatchDicts {
    classes: RefCell<Vec<Option<Rc<crate::inductive::Inductive>>>>,
    goals: RefCell<Vec<(u32, Rc<Vec<(Type, Level)>>)>>,
    resolved: RefCell<Vec<(Type, Option<Term>)>>,
}

impl MatchDicts {
    /// The class the `i`-th parameter's type `dom` instantiates, if any, read
    /// once: a parameter's type is the same at every parameter count.
    fn class_at(&self, el: &Elaborator, i: usize, dom: &Type) -> Option<Rc<crate::inductive::Inductive>> {
        if let Some(c) = self.classes.borrow().get(i) {
            return c.clone();
        }
        let class = el.display_tag_of(dom).filter(|ind| {
            ind.is_record && el.traits.has_class(&crate::names::qkey(&ind.scope.module, &ind.name))
        });
        let mut classes = self.classes.borrow_mut();
        debug_assert_eq!(classes.len(), i, "parameters are read in order");
        classes.push(class.clone());
        class
    }

    /// The class's instantiations the dictionaries in scope answer,
    /// innermost first: for each binder of the class or a descendant, the
    /// class at the binder's carrier and at the index the binder passes up
    /// (`Elaborator::scope_index`, the value-slot ladder's step 2).
    fn goals(&self, el: &Elaborator, cx: &Cx, ind: &crate::inductive::Inductive, span: Span) -> Rc<Vec<(Type, Level)>> {
        if let Some((_, g)) = self.goals.borrow().iter().find(|(tag, _)| *tag == ind.tag) {
            return Rc::clone(g);
        }
        let mut out: Vec<(Type, Level)> = Vec::new();
        if ind.params.len() == 1 {
            for d in cx.dicts.iter_inner() {
                let Ok((carrier, clvl)) = el.elab_ty(cx, &d.carrier) else { continue };
                let Some(index) = el.scope_index(cx, &ind.name, &carrier, &clvl) else { continue };
                let targs = [(carrier, clvl)];
                let Ok(vargs) = el.valparam_args(cx, ind, &targs, &index, span) else { continue };
                let Ok((goal, glvl)) = el.lower_instance(cx, ind, &targs, &vargs, span) else { continue };
                if !out.iter().any(|(g, _)| *g == goal) {
                    out.push((goal, glvl));
                }
            }
        }
        let out = Rc::new(out);
        self.goals.borrow_mut().push((ind.tag, Rc::clone(&out)));
        out
    }

    /// Resolution's dictionary for `goal`, asked once.
    fn resolved(&self, el: &Elaborator, cx: &Cx, goal: &Type, lvl: &Level, name: &str, span: Span) -> Option<Term> {
        if let Some((_, t)) = self.resolved.borrow().iter().find(|(g, _)| g == goal) {
            return t.clone();
        }
        let t = el.resolve_goal(cx, goal, lvl, name, None, span, &mut Vec::new());
        self.resolved.borrow_mut().push((goal.clone(), t.clone()));
        t
    }
}

/// An `Expr`, as the host reads one back from a tactic.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum RExpr {
    /// A handle the host issued.
    Hd(u64),
    /// A local: one of the goal's context by its position from the
    /// outermost, one of its `let`s, or one the tactic introduced ([`Run`]).
    Local(u64),
    App(Box<RExpr>, Box<RExpr>),
    NatLit(u64),
    /// `Lam(x, body)`: abstract the opened local `x` out of `body`.
    Lam(u64, Box<RExpr>),
    /// A global the run issued a reference to.
    Global(u64),
    /// An argument left to inference: a hole at the domain it fills.
    Blank,
    /// `Pi(x, body)`: the function type abstracting the introduced local
    /// `x` out of the type `body`.
    Pi(u64, Box<RExpr>),
    /// The equation between two terms.
    Equation(Box<RExpr>, Box<RExpr>),
}

impl RExpr {
    /// Does a `Blank` occur in it? Each reading of one is a new hole.
    fn has_blank(&self) -> bool {
        match self {
            RExpr::Blank => true,
            RExpr::App(f, a) | RExpr::Equation(f, a) => f.has_blank() || a.has_blank(),
            RExpr::Lam(_, b) | RExpr::Pi(_, b) => b.has_blank(),
            RExpr::Hd(_) | RExpr::Local(_) | RExpr::NatLit(_) | RExpr::Global(_) => false,
        }
    }

    /// Every local this `Expr` names outright, not through a handle.
    fn locals(&self, out: &mut Vec<u64>) {
        match self {
            RExpr::Local(x) => out.push(*x),
            RExpr::App(f, a) | RExpr::Equation(f, a) => {
                f.locals(out);
                a.locals(out);
            }
            RExpr::Lam(_, body) | RExpr::Pi(_, body) => body.locals(out),
            RExpr::Hd(_) | RExpr::NatLit(_) | RExpr::Global(_) | RExpr::Blank => {}
        }
    }

    /// Does this stand for a type by its form (`Pi`, `Equation`), rather
    /// than possibly for a term?
    fn is_type_form(&self) -> bool {
        matches!(self, RExpr::Pi(..) | RExpr::Equation(..))
    }
}

/// One note of a failure's search state (`tactic::Note`), as the host
/// renders it.
#[derive(Clone, Debug)]
pub enum NoteView {
    Tried(String, String),
    Under(Box<NoteView>),
    /// A note about a term, which the host spells.
    At(RExpr, Box<NoteView>),
}

/// One local of the goal's context, as the `Goal` request answers it.
#[derive(Clone, Debug)]
pub struct LocalView {
    pub id: u64,
    pub name: String,
    /// A handle to the local's type.
    pub ty: u64,
}

/// The goal, as the `Goal` request answers it: a handle to its statement and
/// its locals, the most recent first.
#[derive(Clone, Debug)]
pub struct GoalView {
    pub target: u64,
    pub locals: Vec<LocalView>,
}

/// A binder `Open` introduced: its local, a handle to its body, and whether
/// the body mentions the local.
#[derive(Clone, Debug)]
pub struct OpenedView {
    pub local: LocalView,
    pub body: u64,
    pub dependent: bool,
}

/// One branch of a split: its new locals, oldest first, and its goal.
#[derive(Clone, Debug)]
pub struct BranchView {
    pub locals: Vec<LocalView>,
    pub goal: u64,
}

/// A split, as `Cases` and `Constructor` answer it.
#[derive(Clone, Debug)]
pub struct SplitView {
    pub id: u64,
    pub branches: Vec<BranchView>,
}

/// One constructor, as `Ctors` answers it: its name, each field's name
/// (empty for an unnamed one) and a handle to its type (`None` for one that
/// mentions an earlier field), and a handle to the constructor as a function
/// of its fields where every field has one.
#[derive(Clone, Debug)]
pub struct CtorView {
    pub name: String,
    pub fields: Vec<(String, Option<u64>)>,
    pub ctor: Option<u64>,
}

/// One declaration a generator publishes (`tactic::Decl`): its parameters
/// are introduced locals with their implicitness, and its statement and body
/// live under the last of them.
#[derive(Clone, Debug)]
pub struct DeclView {
    pub theorem: bool,
    /// `AsValue`: a `def`, which takes no parameters.
    pub value: bool,
    /// `AsInstance(class, args, index)`: a `def` that is also registered as
    /// the instance `class<args…>(index…)`, the index arguments by name.
    pub instance: Option<(String, Vec<RExpr>, Vec<String>)>,
    pub name: String,
    pub params: Vec<(u64, bool)>,
    pub result: RExpr,
    pub body: RExpr,
}

/// A request, as the host receives it from either kind of tactic.
#[derive(Clone, Debug)]
pub enum Request {
    Goal,
    Defeq(RExpr, RExpr),
    /// The message and its search state, which the host renders.
    Fail(String, Vec<NoteView>),
    Infer(RExpr),
    /// A handle to a function type, and the name of the local to introduce.
    Open(u64, String),
    Resolve(String),
    View(u64),
    Whnf(u64),
    /// A function type's handle and the target's.
    Match(u64, u64),
    /// A hole of the type a handle stands for.
    Hole(u64),
    Mark,
    Restore(u64),
    Lookup(String),
    /// The scrutinee and the goal's handle.
    Cases(RExpr, u64),
    Constructor(u64),
    /// A split's number and one proof per branch.
    Close(u64, Vec<RExpr>),
    /// The type, the local's name, and the local it is introduced under.
    Assume(RExpr, String, Option<u64>),
    Ctors(u64),
    AsType(RExpr),
    /// A term, and how many holes to apply it to.
    Holes(RExpr, u64),
    /// A generator's declarations, which end its run.
    Publish(Vec<DeclView>),
    /// A global's elaborated value, by its reference.
    Body(u64),
    /// The `match` a handle stands for, with its arms.
    Arms(u64),
    /// A type's handle, to be inhabited by `:= infer`'s search.
    Synth(u64),
    /// A term's application spine, by its handle.
    Spine(u64),
    /// The fields of a one-constructor value.
    Fields(RExpr),
    /// The equation between field `k` of the two sides of a proof of an
    /// equation between one constructor's values (`inj`).
    Inj(RExpr, u64),
    /// A proof of the type a handle holds, from a proof of an equation
    /// between two different constructors' values (`absurd`).
    Absurd(RExpr, u64),
    /// What a run says about itself, rendered like `Fail`'s message and
    /// notes, and reported only if the run succeeds.
    Say(String, Vec<NoteView>),
}

/// One layer of a handle, as `View` answers it (`tactic::Head`).
#[derive(Clone, Debug)]
pub enum HeadView {
    Pi(u64),
    Eq(u64, u64),
    /// The global's reference, its name, and the written arguments.
    Global(u64, String, Vec<u64>),
    Local(u64, Vec<u64>),
    /// A field read a record's declaration left inline: the record, the
    /// field's name, and the arguments the field is applied to.
    Field(u64, String, Vec<u64>),
    Lit(u64),
    /// A `match` stuck on the scrutinee.
    Match(u64),
    /// A hole nothing has solved.
    Hole,
    /// A λ, by a handle to its domain.
    Lam(u64),
    /// A constructor value: its type's reference, the constructor's number
    /// and name, and its fields in declaration order.
    Ctor(u64, u64, String, Vec<u64>),
    Other,
}

/// A `match` with its arms, as `Arms` answers it (`tactic::MatchInfo`): the
/// scrutinee, each constructor's name and a handle to its arm as a function
/// of the payload, and the arguments the match is applied to.
#[derive(Clone, Debug)]
pub struct ArmsView {
    pub scrut: u64,
    pub arms: Vec<(String, u64)>,
    pub args: Vec<u64>,
}

/// A term's application spine, as `Spine` answers it (`tactic::SpineInfo`):
/// the head, and every argument it is applied to (implicit ones included),
/// each with whether the function's type at that argument is dependent.
#[derive(Clone, Debug)]
pub struct SpineView {
    pub head: u64,
    pub args: Vec<(u64, bool)>,
}

/// An answer, at the request's own kind. `Err` carries the reason a request
/// that may be refused was.
#[derive(Clone, Debug)]
pub enum Answer {
    Goal(GoalView),
    Bool(bool),
    Handle(Result<u64, String>),
    Opened(Result<OpenedView, String>),
    Head(HeadView),
    /// A match's slots: a handle where the match determined the parameter.
    Match(Result<Vec<Option<u64>>, String>),
    /// `Mark`'s mark.
    Nat(u64),
    /// `Restore` has nothing to say.
    Unit,
    /// A global reference, from `Lookup`.
    Global(Result<u64, String>),
    Split(Result<SplitView, String>),
    /// An `Assume`d local.
    Local(Result<LocalView, String>),
    Ctors(Result<Vec<CtorView>, String>),
    /// The holes `Holes` made.
    Holes(Result<Vec<u64>, String>),
    Arms(Result<ArmsView, String>),
    Spine(Result<SpineView, String>),
    /// The type's reference, and each field's name and a handle to its
    /// projection (`Fields`).
    Fields(Result<(u64, Vec<(String, u64)>), String>),
}

/// Where a tactic is after its last answer.
#[derive(Clone, Debug)]
pub enum Step {
    Done(RExpr),
    Ask(Request),
}

/// A tactic implemented in Rust, speaking the same protocol as `Tac<Expr>`
/// (design §8a): `start` yields its first request or its result, and each
/// `resume` receives the answer to the request it last yielded.
pub trait NativeTactic {
    fn start(&mut self) -> Result<Step, String>;
    fn resume(&mut self, answer: Answer) -> Result<Step, String>;
}

/// The protocol from the host's side: the loop in [`Elaborator::run_tactic`]
/// drives every tactic through this.
trait Speaker {
    fn start(&mut self) -> Result<Step, String>;
    fn resume(&mut self, answer: Answer) -> Result<Step, String>;
}

impl Speaker for Box<dyn NativeTactic> {
    fn start(&mut self) -> Result<Step, String> {
        (**self).start()
    }
    fn resume(&mut self, answer: Answer) -> Result<Step, String> {
        (**self).resume(answer)
    }
}

/// A Heather `Tac<Expr>`, evaluated in the value domain over `world`.
struct Interpreted<'a, 'w, 'v> {
    elab: &'a Elaborator,
    world: &'w GlobalCtx,
    reader: Reader<'w, 'v>,
    arena: &'v ValueArena<'v>,
    tree: &'v TmClo<'v>,
    /// Each `host_*` function's head and rescoped type, looked up once per
    /// run: rescoping a signature is a walk of it, and the loop calls the
    /// same few functions at every step.
    globals: std::cell::RefCell<std::collections::HashMap<&'static str, (Term, Rc<Type>)>>,
}

impl<'a, 'w, 'v> Interpreted<'a, 'w, 'v> {
    /// `tactic::name(args…)` as a pending application over closures. The
    /// `host_*` functions are first-order, so each codomain is used as is.
    fn global(&self, name: &'static str) -> Result<(Term, Rc<Type>), String> {
        if let Some(hit) = self.globals.borrow().get(name) {
            return Ok(hit.clone());
        }
        let key = format!("tactic::{name}");
        let abs = self.elab.global_abs(&key).ok_or_else(|| {
            format!("`{key}` is not declared; `by` needs the protocol from `import tactic;`")
        })?;
        let GlobalBinding::Tm { ty, .. } = &self.world.bindings[abs] else {
            return Err(format!("`{key}` is not a term-level global"));
        };
        let len = self.world.bindings.len();
        let empty = LocalCtx::nil();
        let ty = Rc::new(ty.shift_global((len - abs) as u32));
        let head = Term::GlobalTm {
            var: GlobalVar((len - 1 - abs) as u32),
            subst: LocalSubst::id(&empty),
        };
        self.globals.borrow_mut().insert(name, (head.clone(), Rc::clone(&ty)));
        Ok((head, ty))
    }

    fn call(&self, name: &'static str, args: Vec<&'v TmClo<'v>>) -> Result<&'v TmClo<'v>, String> {
        let (head, ty) = self.global(name)?;
        let key = name;
        let mut ty: &Type = &ty;
        let mut out = self.arena.tm(TmClo::syn(Env::empty(), Rc::new(head)));
        for arg in args {
            let Type::Pi { dom_level, cod_level, dom, cod } = ty else {
                return Err(format!("`tactic::{key}`'s signature ran out of parameters"));
            };
            let elim = Elim::App {
                ann: Some(PiAnn {
                    dom_level: dom_level.clone(),
                    cod_level: cod_level.clone(),
                    dom: self.arena.ty(TyClo::new(Env::empty(), Rc::clone(dom))),
                    cod: self.arena.ty(TyClo::new(Env::empty(), Rc::clone(cod))),
                }),
                arg,
            };
            out = self.arena.tm(TmClo::elim(out, self.arena.elim_cell(elim)));
            ty = cod;
        }
        Ok(out)
    }

    fn lit(&self, n: u64) -> &'v TmClo<'v> {
        self.reader.root(crate::inductive::nat_lit(n as usize))
    }

    fn nat_of(&self, name: &'static str, args: Vec<&'v TmClo<'v>>) -> Result<u64, String> {
        self.reader
            .nat(self.call(name, args)?)
            .map_err(|e| {
                if e.contains("fuel") {
                    "evaluating the tactic ran out of fuel or nesting depth".to_string()
                } else {
                    e
                }
            })
    }

    fn expr(&self, e: &'v TmClo<'v>, budget: &mut usize) -> Result<RExpr, String> {
        if *budget == 0 {
            return Err("the tactic returned an implausibly large `Expr`".into());
        }
        *budget -= 1;
        match self.nat_of("expr_tag", vec![e])? {
            0 => Ok(RExpr::Hd(self.nat_of("expr_nat", vec![e])?)),
            1 => Ok(RExpr::Local(self.nat_of("expr_nat", vec![e])?)),
            2 => {
                let f = self.expr(self.call("expr_fn", vec![e])?, budget)?;
                let a = self.expr(self.call("expr_arg", vec![e])?, budget)?;
                Ok(RExpr::App(Box::new(f), Box::new(a)))
            }
            3 => Ok(RExpr::NatLit(self.nat_of("expr_nat", vec![e])?)),
            4 => {
                let x = self.nat_of("expr_nat", vec![e])?;
                let body = self.expr(self.call("expr_arg", vec![e])?, budget)?;
                Ok(RExpr::Lam(x, Box::new(body)))
            }
            5 => Ok(RExpr::Global(self.nat_of("expr_nat", vec![e])?)),
            6 => Ok(RExpr::Blank),
            7 => {
                let x = self.nat_of("expr_nat", vec![e])?;
                let body = self.expr(self.call("expr_arg", vec![e])?, budget)?;
                Ok(RExpr::Pi(x, Box::new(body)))
            }
            8 => {
                let l = self.expr(self.call("expr_fn", vec![e])?, budget)?;
                let r = self.expr(self.call("expr_arg", vec![e])?, budget)?;
                Ok(RExpr::Equation(Box::new(l), Box::new(r)))
            }
            other => Err(format!("an `Expr` with tag {other}")),
        }
    }

    fn note(&self, n: &'v TmClo<'v>, budget: &mut usize) -> Result<NoteView, String> {
        if *budget == 0 {
            return Err("the tactic failed with an implausibly large note".into());
        }
        *budget -= 1;
        match self.nat_of("note_tag", vec![n])? {
            0 => Ok(NoteView::Tried(
                self.string(self.call("note_what", vec![n])?)?,
                self.string(self.call("note_verdict", vec![n])?)?,
            )),
            1 => Ok(NoteView::Under(Box::new(self.note(self.call("note_inner", vec![n])?, budget)?))),
            2 => {
                let e = self.expr(self.call("note_expr", vec![n])?, budget)?;
                Ok(NoteView::At(e, Box::new(self.note(self.call("note_inner", vec![n])?, budget)?)))
            }
            other => Err(format!("a `Note` with tag {other}")),
        }
    }

    /// A failure's message and notes, or what `Say` says.
    fn failure(&self) -> Result<(String, Vec<NoteView>), String> {
        let tree = self.tree;
        let msg = self.string(self.call("host_failure", vec![tree])?)?;
        let count = self.nat_of("host_note_count", vec![tree])?;
        let mut budget = READ_BUDGET;
        let mut notes = Vec::new();
        for i in 0..count {
            notes.push(self.note(self.call("host_note", vec![tree, self.lit(i)])?, &mut budget)?);
        }
        Ok((msg, notes))
    }

    /// `Publish`'s declarations, one at a time and each part by itself.
    fn decls(&self) -> Result<Request, String> {
        let tree = self.tree;
        let count = self.nat_of("host_decl_count", vec![tree])?;
        let mut budget = READ_BUDGET;
        let mut decls = Vec::new();
        for i in 0..count {
            let d = self.call("host_decl", vec![tree, self.lit(i)])?;
            let params = (0..self.nat_of("decl_param_count", vec![d])?)
                .map(|j| {
                    let x = self.nat_of("decl_param", vec![d, self.lit(j)])?;
                    Ok((x, self.nat_of("decl_param_implicit", vec![d, self.lit(j)])? != 0))
                })
                .collect::<Result<Vec<_>, String>>()?;
            let form = self.nat_of("decl_form", vec![d])?;
            let instance = if form == 3 {
                let class = self.string(self.call("decl_instance_class", vec![d])?)?;
                let args = (0..self.nat_of("decl_instance_arg_count", vec![d])?)
                    .map(|j| self.expr(self.call("decl_instance_arg", vec![d, self.lit(j)])?, &mut budget))
                    .collect::<Result<Vec<_>, String>>()?;
                let index = (0..self.nat_of("decl_instance_index_count", vec![d])?)
                    .map(|j| self.string(self.call("decl_instance_index", vec![d, self.lit(j)])?))
                    .collect::<Result<Vec<_>, String>>()?;
                Some((class, args, index))
            } else {
                None
            };
            decls.push(DeclView {
                theorem: form == 0,
                value: form == 2 || form == 3,
                instance,
                name: self.string(self.call("decl_name", vec![d])?)?,
                params,
                result: self.expr(self.call("decl_result", vec![d])?, &mut budget)?,
                body: self.expr(self.call("decl_body", vec![d])?, &mut budget)?,
            });
        }
        Ok(Request::Publish(decls))
    }

    fn string(&self, s: &'v TmClo<'v>) -> Result<String, String> {
        let len = self.nat_of("str_len", vec![s])?;
        let shown = (len as usize).min(READ_BUDGET);
        let mut out = String::with_capacity(shown);
        for i in 0..shown {
            let code = self.nat_of("str_code", vec![s, self.lit(i as u64)])?;
            out.push(char::from_u32(code as u32).unwrap_or('\u{FFFD}'));
        }
        if shown < len as usize {
            out.push('…');
        }
        Ok(out)
    }

    fn string_value(&self, s: &str) -> Result<&'v TmClo<'v>, String> {
        let mut out = self.call("str_empty", vec![])?;
        for c in s.chars() {
            out = self.call("str_push", vec![out, self.lit(c as u64)])?;
        }
        Ok(out)
    }

    fn answer(&self, a: &Answer) -> Result<&'v TmClo<'v>, String> {
        match a {
            Answer::Bool(b) => self.call("host_bool", vec![self.lit(*b as u64)]),
            Answer::Goal(g) => {
                let mut out = self.call("host_goal", vec![self.lit(g.target)])?;
                for l in &g.locals {
                    let name = self.string_value(&l.name)?;
                    out = self.call("host_goal_local", vec![out, self.lit(l.id), name, self.lit(l.ty)])?;
                }
                Ok(out)
            }
            Answer::Handle(Ok(h)) => self.call("host_accepted", vec![self.lit(*h)]),
            Answer::Handle(Err(why)) => self.call("host_refused", vec![self.string_value(why)?]),
            Answer::Opened(Ok(o)) => {
                let name = self.string_value(&o.local.name)?;
                self.call(
                    "host_opened",
                    vec![self.lit(o.local.id), name, self.lit(o.local.ty), self.lit(o.body), self.lit(o.dependent as u64)],
                )
            }
            Answer::Opened(Err(why)) => self.call("host_not_opened", vec![self.string_value(why)?]),
            Answer::Head(v) => {
                let (mut out, args) = match v {
                    HeadView::Pi(dom) => return self.call("host_head_pi", vec![self.lit(*dom)]),
                    HeadView::Eq(l, r) => return self.call("host_head_eq", vec![self.lit(*l), self.lit(*r)]),
                    HeadView::Lit(n) => return self.call("host_head_lit", vec![self.lit(*n)]),
                    HeadView::Match(s) => return self.call("host_head_match", vec![self.lit(*s)]),
                    HeadView::Hole => return self.call("host_head_hole", vec![]),
                    HeadView::Lam(dom) => return self.call("host_head_lam", vec![self.lit(*dom)]),
                    HeadView::Ctor(ty, i, name, fields) => {
                        (self.call("host_head_ctor", vec![self.lit(*ty), self.lit(*i), self.string_value(name)?])?, fields)
                    }
                    HeadView::Other => return self.call("host_head_other", vec![]),
                    HeadView::Global(g, name, args) => {
                        (self.call("host_head_global", vec![self.lit(*g), self.string_value(name)?])?, args)
                    }
                    HeadView::Local(x, args) => (self.call("host_head_local", vec![self.lit(*x)])?, args),
                    HeadView::Field(r, name, args) => {
                        (self.call("host_head_field", vec![self.lit(*r), self.string_value(name)?])?, args)
                    }
                };
                for h in args {
                    out = self.call("host_head_arg", vec![out, self.lit(*h)])?;
                }
                Ok(out)
            }
            Answer::Match(Ok(slots)) => {
                let mut out = self.call("host_matched", vec![])?;
                for slot in slots {
                    out = match slot {
                        Some(h) => self.call("host_slot", vec![out, self.lit(*h)])?,
                        None => self.call("host_open_slot", vec![out])?,
                    };
                }
                Ok(out)
            }
            Answer::Match(Err(why)) => self.call("host_not_matched", vec![self.string_value(why)?]),
            Answer::Nat(n) => self.call("host_nat", vec![self.lit(*n)]),
            Answer::Unit => self.call("host_unit", vec![]),
            Answer::Global(Ok(g)) => self.call("host_global", vec![self.lit(*g)]),
            Answer::Global(Err(why)) => self.call("host_no_global", vec![self.string_value(why)?]),
            Answer::Split(Ok(split)) => {
                let mut out = self.call("host_split", vec![self.lit(split.id)])?;
                for b in &split.branches {
                    out = self.call("host_branch", vec![out, self.lit(b.goal)])?;
                    for l in &b.locals {
                        let name = self.string_value(&l.name)?;
                        out = self.call("host_branch_local", vec![out, self.lit(l.id), name, self.lit(l.ty)])?;
                    }
                }
                Ok(out)
            }
            Answer::Split(Err(why)) => self.call("host_split_refused", vec![self.string_value(why)?]),
            Answer::Local(Ok(l)) => {
                let name = self.string_value(&l.name)?;
                self.call("host_assumed", vec![self.lit(l.id), name, self.lit(l.ty)])
            }
            Answer::Local(Err(why)) => self.call("host_not_assumed", vec![self.string_value(why)?]),
            Answer::Ctors(Ok(cs)) => {
                let mut out = self.call("host_ctors", vec![])?;
                for c in cs {
                    out = self.call("host_ctor", vec![out, self.string_value(&c.name)?])?;
                    for (name, f) in &c.fields {
                        let name = self.string_value(name)?;
                        out = match f {
                            Some(h) => self.call("host_ctor_field", vec![out, name, self.lit(*h)])?,
                            None => self.call("host_ctor_dependent_field", vec![out, name])?,
                        };
                    }
                    if let Some(h) = c.ctor {
                        out = self.call("host_ctor_fn", vec![out, self.lit(h)])?;
                    }
                }
                Ok(out)
            }
            Answer::Ctors(Err(why)) => self.call("host_ctors_refused", vec![self.string_value(why)?]),
            Answer::Holes(Ok(hs)) => {
                let mut out = self.call("host_holes", vec![])?;
                for h in hs {
                    out = self.call("host_holes_next", vec![out, self.lit(*h)])?;
                }
                Ok(out)
            }
            Answer::Holes(Err(why)) => self.call("host_no_holes", vec![self.string_value(why)?]),
            Answer::Arms(Ok(m)) => {
                let mut out = self.call("host_arms", vec![self.lit(m.scrut)])?;
                for (ctor, body) in &m.arms {
                    out = self.call("host_arms_arm", vec![out, self.string_value(ctor)?, self.lit(*body)])?;
                }
                for h in &m.args {
                    out = self.call("host_arms_arg", vec![out, self.lit(*h)])?;
                }
                Ok(out)
            }
            Answer::Arms(Err(why)) => self.call("host_no_arms", vec![self.string_value(why)?]),
            Answer::Spine(Ok(sp)) => {
                let mut out = self.call("host_spine", vec![self.lit(sp.head)])?;
                for (h, dependent) in &sp.args {
                    out = self.call("host_spine_arg", vec![out, self.lit(*h), self.lit(*dependent as u64)])?;
                }
                Ok(out)
            }
            Answer::Spine(Err(why)) => self.call("host_no_spine", vec![self.string_value(why)?]),
            Answer::Fields(Ok((ty, fs))) => {
                let mut out = self.call("host_fields", vec![self.lit(*ty)])?;
                for (name, h) in fs {
                    out = self.call("host_fields_next", vec![out, self.string_value(name)?, self.lit(*h)])?;
                }
                Ok(out)
            }
            Answer::Fields(Err(why)) => self.call("host_no_fields", vec![self.string_value(why)?]),
        }
    }

    fn step(&self) -> Result<Step, String> {
        let tree = self.tree;
        match self.nat_of("host_tag", vec![tree])? {
            0 => {
                let mut budget = READ_BUDGET;
                Ok(Step::Done(self.expr(self.call("host_result", vec![tree])?, &mut budget)?))
            }
            1 => Ok(Step::Ask(Request::Goal)),
            2 => {
                let mut budget = READ_BUDGET;
                let a = self.expr(self.call("host_lhs", vec![tree])?, &mut budget)?;
                let b = self.expr(self.call("host_rhs", vec![tree])?, &mut budget)?;
                Ok(Step::Ask(Request::Defeq(a, b)))
            }
            3 => {
                let (msg, notes) = self.failure()?;
                Ok(Step::Ask(Request::Fail(msg, notes)))
            }
            4 => {
                let mut budget = READ_BUDGET;
                Ok(Step::Ask(Request::Infer(self.expr(self.call("host_lhs", vec![tree])?, &mut budget)?)))
            }
            5 => {
                let h = self.nat_of("host_handle", vec![tree])?;
                Ok(Step::Ask(Request::Open(h, self.string(self.call("host_name", vec![tree])?)?)))
            }
            6 => Ok(Step::Ask(Request::Resolve(self.string(self.call("host_name", vec![tree])?)?))),
            7 => Ok(Step::Ask(Request::View(self.nat_of("host_handle", vec![tree])?))),
            8 => Ok(Step::Ask(Request::Whnf(self.nat_of("host_handle", vec![tree])?))),
            9 => Ok(Step::Ask(Request::Match(
                self.nat_of("host_handle", vec![tree])?,
                self.nat_of("host_target", vec![tree])?,
            ))),
            10 => Ok(Step::Ask(Request::Hole(self.nat_of("host_handle", vec![tree])?))),
            11 => Ok(Step::Ask(Request::Mark)),
            12 => Ok(Step::Ask(Request::Restore(self.nat_of("host_mark", vec![tree])?))),
            13 => Ok(Step::Ask(Request::Lookup(self.string(self.call("host_name", vec![tree])?)?))),
            14 => {
                let mut budget = READ_BUDGET;
                let e = self.expr(self.call("host_lhs", vec![tree])?, &mut budget)?;
                Ok(Step::Ask(Request::Cases(e, self.nat_of("host_handle", vec![tree])?)))
            }
            15 => Ok(Step::Ask(Request::Constructor(self.nat_of("host_handle", vec![tree])?))),
            16 => {
                let split = self.nat_of("host_split_id", vec![tree])?;
                let count = self.nat_of("host_proof_count", vec![tree])?;
                let mut budget = READ_BUDGET;
                let mut proofs = Vec::new();
                for i in 0..count {
                    proofs.push(self.expr(self.call("host_proof", vec![tree, self.lit(i)])?, &mut budget)?);
                }
                Ok(Step::Ask(Request::Close(split, proofs)))
            }
            17 => {
                let mut budget = READ_BUDGET;
                let ty = self.expr(self.call("host_lhs", vec![tree])?, &mut budget)?;
                let name = self.string(self.call("host_name", vec![tree])?)?;
                let under = self.nat_of("host_under", vec![tree])?.checked_sub(1);
                Ok(Step::Ask(Request::Assume(ty, name, under)))
            }
            18 => Ok(Step::Ask(Request::Ctors(self.nat_of("host_handle", vec![tree])?))),
            19 => {
                let mut budget = READ_BUDGET;
                Ok(Step::Ask(Request::AsType(self.expr(self.call("host_lhs", vec![tree])?, &mut budget)?)))
            }
            20 => Ok(Step::Ask(self.decls()?)),
            21 => {
                let mut budget = READ_BUDGET;
                let e = self.expr(self.call("host_lhs", vec![tree])?, &mut budget)?;
                Ok(Step::Ask(Request::Holes(e, self.nat_of("host_hole_count", vec![tree])?)))
            }
            22 => Ok(Step::Ask(Request::Body(self.nat_of("host_handle", vec![tree])?))),
            23 => Ok(Step::Ask(Request::Arms(self.nat_of("host_handle", vec![tree])?))),
            24 => Ok(Step::Ask(Request::Synth(self.nat_of("host_handle", vec![tree])?))),
            25 => Ok(Step::Ask(Request::Spine(self.nat_of("host_handle", vec![tree])?))),
            26 => {
                let (msg, notes) = self.failure()?;
                Ok(Step::Ask(Request::Say(msg, notes)))
            }
            27 => {
                let mut budget = READ_BUDGET;
                Ok(Step::Ask(Request::Fields(self.expr(self.call("host_lhs", vec![tree])?, &mut budget)?)))
            }
            28 => {
                let mut budget = READ_BUDGET;
                let e = self.expr(self.call("host_lhs", vec![tree])?, &mut budget)?;
                Ok(Step::Ask(Request::Inj(e, self.nat_of("host_hole_count", vec![tree])?)))
            }
            29 => {
                let mut budget = READ_BUDGET;
                let e = self.expr(self.call("host_lhs", vec![tree])?, &mut budget)?;
                Ok(Step::Ask(Request::Absurd(e, self.nat_of("host_handle", vec![tree])?)))
            }
            other => Err(format!("a request tree with tag {other}")),
        }
    }
}

impl Speaker for Interpreted<'_, '_, '_> {
    fn start(&mut self) -> Result<Step, String> {
        self.step()
    }

    fn resume(&mut self, answer: Answer) -> Result<Step, String> {
        let a = self.answer(&answer)?;
        self.tree = self.pin(self.call("host_resume", vec![self.tree, a])?)?;
        self.step()
    }
}

impl<'v> Interpreted<'_, '_, 'v> {
    /// The tree as a value whose two components are values too.
    ///
    /// `Tac` is tier 2, `Σ(t : W). canon t` (docs/inductive-tier2-w-lowering.md
    /// §5), and `host_resume`'s `match` rebuilds the continuation as
    /// `k := λy. ⟨f' y, c y⟩` with `c` the scrutinee's *proof*, `snd t`
    /// (§7). So the resumed tree's proof is the previous tree's proof
    /// applied, and nothing forces it until a leaf arm's `J` does: left
    /// pending, the proof of the n-th tree is a chain of n projections, and
    /// forcing it at the final `Pure` stood on one native frame per answered
    /// request, which capped a run near `NATIVE_DEPTH_LIMIT` requests
    /// (issues/tactic-run-continuation-chain.md). Forcing both components here,
    /// one step at a time, and handing the next `host_resume` closures that
    /// *are* values, keeps every chain one link long whatever the cache keeps.
    ///
    /// This is the only place the host looks at the lowering, and only at its
    /// outer pair; a value of any other shape is left as it is.
    fn pin(&self, tree: &'v TmClo<'v>) -> Result<&'v TmClo<'v>, String> {
        let force = |c| {
            self.reader.force(c).map_err(|_| "evaluating the tactic ran out of fuel or nesting depth".to_string())
        };
        let v = force(tree)?;
        let Val::Pair { ann, fst, snd } = &*v else {
            return Ok(tree);
        };
        let fst = self.arena.tm(TmClo::val(force(fst)?));
        let snd = self.arena.tm(TmClo::val(force(snd)?));
        Ok(self.arena.tm(TmClo::val(self.arena.val(Val::Pair { ann: ann.clone(), fst, snd }))))
    }
}

/// One context the host answers requests in: the goal's, or a binder's body
/// that `Open` introduced under its `parent`.
struct Scope {
    parent: Option<usize>,
    /// Its context, in the world of the first `world` holes (see [`Run`]).
    cx: Cx,
    world: usize,
    /// The ids of the locals this scope adds to its parent's context, in
    /// order: an opened binder's one local, a branch's fields and equation.
    locals: Vec<u64>,
}

/// What a handle stands for.
#[derive(Clone)]
pub(crate) enum Held {
    Type(Type, Level),
    Term(Term, Type, Level),
}

/// A handle: what it stands for, in which scope, and in the world of how
/// many holes.
struct Issued {
    scope: usize,
    world: usize,
    held: Held,
}

/// A hole `Hole` made: a metavariable of its `home` scope. Its type is its
/// handle's.
struct Hole {
    home: usize,
    /// Its solution: a term of the committed world, scoped in `home`'s
    /// context.
    sol: Option<Rc<Term>>,
}

/// A global a `GlobalRef` names. References are interned, so the same global
/// has the same number throughout a run.
#[derive(Clone, PartialEq, Eq)]
enum GlobalKey {
    /// A Ψ binding, by its absolute index.
    At(usize),
    /// An inductive type, by its tag.
    Type(u32),
    /// A kernel former the diagnostics give a name (`Nat`, `Succ`, `True`).
    Builtin(&'static str),
}

/// A block `let` in scope at the goal, which a tactic sees as one of the
/// goal's locals: a handle to its value and one to its type, both scoped in
/// the goal's context. A `Local` naming it is its value, as a use of the
/// name in source would be.
struct LetLocal {
    alias: Rc<Alias>,
    value: u64,
    ty: u64,
}

/// Everything one run issued: its scopes, its handles (each in a scope),
/// the locals its scopes introduced, its holes, the global references it
/// handed out and its splits. Ids of the goal's own locals are their
/// positions in its context; the goal's `let`s come next, by their index in
/// `lets`; any other local's id is the goal's length plus the number of
/// `let`s plus its index in `opened`.
///
/// **Holes are metavariables in the elaborator's scratch-world form**
/// (`unification.rs`): with `m` holes, a term of the run lives in Ψ extended
/// by `m` bindings, the newest hole innermost, so hole `j` is the global at
/// index `m - 1 - j` and every committed global sits `m` further out. A
/// hole's occurrence is `GlobalTm` with its home scope's identity
/// substitution, weakened like any term. Each handle records the world it was
/// issued in and is shifted up on use. Nothing of the kernel ever sees such a
/// term: a request zonks first, and a term with an unsolved hole gets only
/// what the request can answer from its structure.
struct Run {
    scopes: Vec<Scope>,
    held: Vec<Issued>,
    lets: Vec<LetLocal>,
    /// Each introduced local's scope and position there.
    opened: Vec<(usize, usize)>,
    holes: Vec<Hole>,
    /// Holes in the order they were solved; a mark is a length of it.
    trail: Vec<usize>,
    globals: Vec<GlobalKey>,
    splits: Vec<Rc<Split>>,
    span: Span,
    /// A generator's run (`generate`): its root is the module's empty
    /// context, it has no goal, and it ends by publishing.
    generator: bool,
    /// Applications already reified, by scope and `Expr`: a tactic builds an
    /// application one argument at a time and asks for each prefix's type
    /// (`apply_slots`, `cast_holes`), so each request re-reads the prefix
    /// before it. A hit is the earlier reading, in the world it was made in
    /// and valid while the hole solutions it was made under stand
    /// ([`Reading`]).
    readings: std::collections::HashMap<(usize, RExpr), Reading>,
    /// Handles issued for subterms, by scope and the subterm's address, so
    /// a subterm a term shares (a block's `let` is an alias, not a binder)
    /// is one handle wherever a view meets it in that scope
    /// (docs/runtime-fn-setups-design.md §3.2). The `Rc` held here keeps the
    /// address from being reused while the run lasts.
    shared: std::collections::HashMap<(usize, usize), (Rc<Term>, u64)>,
    /// What the run said (`Say`), reported at its span once it succeeds.
    said: Vec<String>,
}

/// A remembered reification: the world it was made in (its terms are
/// shifted past the holes made since) and the trail's length then. A
/// `Restore` below that length may have forgotten a solution the reading
/// relied on (its argument's type matched the domain by it), so it drops
/// the reading.
struct Reading {
    reified: Reified,
    world: usize,
    trail: usize,
}

/// How a run ended: with a tactic's result, or a generator's declarations.
enum Ended {
    Result(RExpr),
    Published(Vec<DeclView>),
}

/// How a split's proof is built: surface syntax whose leaves are
/// [`leaf_expr`] markers, one per branch.
enum Skeleton {
    /// `match` on an elaborated scrutinee, at a motive, with the equation
    /// binder named `equation` (the elaborator's convoy).
    Cases { scrut: Term, ty: Type, level: Level, motive: Type, equation: String, arms: Vec<heather_syntax::Arm> },
    /// A constructor application, checked at the goal.
    Constructor(Expr),
}

/// A split the run issued: the scope and goal it splits, how its proof is
/// built, and each branch's scope and goal handle. Everything is committed.
struct Split {
    at: usize,
    goal: Type,
    lvl: Level,
    skeleton: Skeleton,
    branches: Vec<(usize, u64)>,
}

/// What a split's leaves do while its skeleton is elaborated.
#[derive(Clone)]
pub(crate) enum Leaves {
    /// Record each leaf's context, statement and level, and stand for it
    /// with `placeholder`.
    Record { placeholder: Term, seen: Vec<Option<(Cx, Type, Level)>> },
    /// Each leaf is its branch's proof, valid in a context of the length
    /// given.
    Fill(Vec<(Term, usize)>),
    /// A generated declaration's parameter types, statement and body
    /// ([`Elaborator::elab_generate`]), in a context of the length given.
    /// They were built in a world of `psi` globals, and the declarations
    /// published since are shifted past.
    Member { fills: Vec<(Held, usize)>, psi: usize },
}

const LEAF: &str = "\0host-leaf-";

/// Leaf `k` of a skeleton. Like the parser's markers, its name cannot be
/// written.
fn leaf_expr(k: usize, span: Span) -> Expr {
    Expr { kind: heather_syntax::ast::ExprKind::Var(format!("{LEAF}{k}")), span }
}

/// The leaf a name marks, if it is one.
pub(crate) fn leaf_index(name: &str) -> Option<usize> {
    name.strip_prefix(LEAF)?.parse().ok()
}

/// Why an `Expr` could not be elaborated. A broken protocol (an id the run
/// never issued, a local outside its binder) ends the run; an ill-typed
/// `Expr` is an answer a tactic can act on.
enum Fault {
    Protocol(String),
    Ill(String),
}

/// A request's outcome as its answer: refused for an ill-typed `Expr`, and
/// the run's end for a broken protocol.
fn refusable<T>(r: Result<T, Fault>) -> Result<Result<T, String>, String> {
    match r {
        Ok(t) => Ok(Ok(t)),
        Err(Fault::Ill(why)) => Ok(Err(why)),
        Err(Fault::Protocol(msg)) => Err(msg),
    }
}

impl Fault {
    fn msg(self) -> String {
        match self {
            Fault::Protocol(m) | Fault::Ill(m) => m,
        }
    }
}

impl Run {
    fn new(cx: &Cx, span: Span, generator: bool) -> Run {
        Run {
            scopes: vec![Scope { parent: None, cx: cx.clone(), world: 0, locals: Vec::new() }],
            held: Vec::new(),
            lets: Vec::new(),
            opened: Vec::new(),
            holes: Vec::new(),
            trail: Vec::new(),
            globals: Vec::new(),
            splits: Vec::new(),
            span,
            generator,
            readings: std::collections::HashMap::new(),
            shared: std::collections::HashMap::new(),
            said: Vec::new(),
        }
    }

    /// The handles an invocation's arguments quoted, in order, at the root.
    fn issue_quoted(&mut self, quoted: Vec<Held>) {
        for held in quoted {
            self.issue(0, held);
        }
    }

    fn len(&self, s: usize) -> usize {
        self.scopes[s].cx.gamma.len()
    }

    /// The number of holes, which is the world every answer is built in.
    fn world(&self) -> usize {
        self.holes.len()
    }

    /// Is `a` the scope `b` or one enclosing it?
    fn encloses(&self, a: usize, mut b: usize) -> bool {
        loop {
            if a == b {
                return true;
            }
            match self.scopes[b].parent {
                Some(p) => b = p,
                None => return false,
            }
        }
    }

    fn join(&self, a: usize, b: usize) -> Result<usize, Fault> {
        if self.encloses(a, b) {
            Ok(b)
        } else if self.encloses(b, a) {
            Ok(a)
        } else {
            Err(Fault::Protocol("the `Expr` uses locals from two different binders".into()))
        }
    }

    /// A handle's scope and what it stands for, in the current world.
    fn held(&self, h: u64) -> Result<(usize, Held), Fault> {
        let issued = self.held.get(h as usize).ok_or_else(|| Fault::Protocol(format!("handle {h} was not issued by this run")))?;
        let by = (self.world() - issued.world) as u32;
        let held = match &issued.held {
            Held::Type(t, l) => Held::Type(t.shift_global(by), l.clone()),
            Held::Term(t, ty, l) => Held::Term(t.shift_global(by), ty.shift_global(by), l.clone()),
        };
        Ok((issued.scope, held))
    }

    /// The id the next introduced local gets.
    fn next_id(&self) -> u64 {
        (self.len(0) + self.lets.len() + self.opened.len()) as u64
    }

    /// The goal's `let` a local id names, if it names one.
    fn let_local(&self, id: u64) -> Option<&LetLocal> {
        self.lets.get((id as usize).checked_sub(self.len(0))?)
    }

    /// The scope a binder's local belongs to and its position in that
    /// scope's context. A `let` has no position; its id is refused here.
    fn local(&self, id: u64) -> Result<(usize, usize), Fault> {
        let root = self.len(0);
        let id = id as usize;
        if id < root {
            return Ok((0, id));
        }
        if let Some(l) = self.lets.get(id - root) {
            return Err(Fault::Protocol(format!("local {id} is the `let` `{}`, which no binder bound", l.alias.name)));
        }
        self.opened
            .get(id - root - self.lets.len())
            .copied()
            .ok_or_else(|| Fault::Protocol(format!("there is no local {id} in this run")))
    }

    /// The type of position `i` of scope `at`'s context, scoped there, in the
    /// current world.
    fn local_ty(&self, at: usize, i: usize) -> (Type, Level) {
        let gamma = &self.scopes[at].cx.gamma;
        let entry = gamma.entries.get(i).expect("a local of an enclosing scope");
        let ty = entry.ty.shift_local((gamma.len() - i) as u32).shift_global((self.world() - self.scopes[at].world) as u32);
        (ty, entry.level.clone())
    }

    /// The deepest scope `e` mentions, which every other one it mentions
    /// must enclose.
    fn scope_of(&self, e: &RExpr) -> Result<usize, Fault> {
        match e {
            RExpr::Hd(h) => Ok(self.held(*h)?.0),
            RExpr::Local(x) if self.let_local(*x).is_some() => Ok(0),
            RExpr::Local(x) => Ok(self.local(*x)?.0),
            RExpr::NatLit(_) | RExpr::Global(_) | RExpr::Blank => Ok(0),
            RExpr::App(f, a) | RExpr::Equation(f, a) => self.join(self.scope_of(f)?, self.scope_of(a)?),
            RExpr::Lam(x, _) | RExpr::Pi(x, _) => {
                let (s, _) = self.local(*x)?;
                self.scopes[s].parent.ok_or_else(|| Fault::Protocol(format!("`Lam` or `Pi` abstracts local {x}, which the tactic did not open")))
            }
        }
    }

    /// A handle's type or term, weakened from its scope to `to`.
    fn lift<T>(&self, from: usize, to: usize, shift: impl FnOnce(u32) -> T) -> Result<T, Fault> {
        if !self.encloses(from, to) {
            return Err(Fault::Protocol("a handle is used outside the binder it lives under".into()));
        }
        Ok(shift((self.len(to) - self.len(from)) as u32))
    }

    /// The id of the local at position `p` of scope `at`'s context.
    fn local_at(&self, at: usize, p: usize) -> Option<u64> {
        if p < self.len(0) {
            return Some(p as u64);
        }
        let mut s = at;
        loop {
            let parent = self.scopes[s].parent?;
            let base = self.len(parent);
            if p >= base {
                return self.scopes[s].locals.get(p - base).copied();
            }
            s = parent;
        }
    }

    /// Issue a handle to a committed term or type.
    fn issue(&mut self, scope: usize, held: Held) -> u64 {
        self.issue_in(scope, 0, held)
    }

    /// A handle to a committed subterm `t` of a term held in `scope`: the
    /// same handle each time the same shared subterm is met there.
    fn issue_shared(&mut self, scope: usize, t: &Rc<Term>, ty: Type, level: Level) -> u64 {
        let key = (scope, Rc::as_ptr(t) as usize);
        if let Some((_, h)) = self.shared.get(&key) {
            return *h;
        }
        let h = self.issue(scope, Held::Term((**t).clone(), ty, level));
        self.shared.insert(key, (Rc::clone(t), h));
        h
    }

    /// Issue a handle to something in the world of `world` holes.
    fn issue_in(&mut self, scope: usize, world: usize, held: Held) -> u64 {
        self.held.push(Issued { scope, world, held });
        (self.held.len() - 1) as u64
    }

    /// A handle to something in the current world, committed if it is.
    fn issue_now(&mut self, scope: usize, held: Held) -> u64 {
        let committed = match &held {
            Held::Type(t, l) => self.committed_ty(t).map(|t| Held::Type(t, l.clone())),
            Held::Term(t, ty, l) => match (self.committed_tm(t), self.committed_ty(ty)) {
                (Some(t), Some(ty)) => Some(Held::Term(t, ty, l.clone())),
                _ => None,
            },
        };
        match committed {
            Some(held) => self.issue(scope, held),
            None => self.issue_in(scope, self.world(), held),
        }
    }

    fn global_ref(&mut self, key: GlobalKey) -> u64 {
        let i = match self.globals.iter().position(|k| *k == key) {
            Some(i) => i,
            None => {
                self.globals.push(key);
                self.globals.len() - 1
            }
        };
        i as u64
    }

    /// The scratch-world slots, the unifier's way round: slot `k` is the
    /// global at index `k`, hole `m - 1 - k`.
    fn sols(&self) -> Vec<Sol> {
        self.holes.iter().rev().map(|h| match &h.sol {
            Some(t) => Sol::Solved(Rc::clone(t)),
            None => Sol::Unsolved,
        }).collect()
    }

    /// The substitution that consumes every hole: each one's solution, or
    /// `unsolved(j)` for hole `j`. Entries run oldest hole first.
    fn sigma(&self, solved_shift: u32, unsolved: impl Fn(usize) -> Term) -> GlobalSubst {
        let entries = self.holes.iter().enumerate().map(|(j, h)| GlobalEntry::Tm(match &h.sol {
            Some(t) => Rc::new(t.shift_global(solved_shift)),
            None => Rc::new(unsolved(j)),
        })).collect();
        GlobalSubst { entries }
    }

    /// `t` in the committed world, if every hole it mentions is solved: the
    /// two-marker test of `unification::zonked`.
    fn committed_ty(&self, t: &Type) -> Option<Type> {
        if self.holes.is_empty() {
            return Some(t.clone());
        }
        let a = t.apply_global(&self.sigma(0, |_| Term::Zero));
        (a == t.apply_global(&self.sigma(0, |_| Term::Succ(Rc::new(Term::Zero))))).then_some(a)
    }

    fn committed_tm(&self, t: &Term) -> Option<Term> {
        if self.holes.is_empty() {
            return Some(t.clone());
        }
        let a = t.apply_global(&self.sigma(0, |_| Term::Zero));
        (a == t.apply_global(&self.sigma(0, |_| Term::Succ(Rc::new(Term::Zero))))).then_some(a)
    }

    /// Hole `j`'s occurrence at its home, in the current world.
    fn occurrence(&self, j: usize) -> Term {
        Term::GlobalTm {
            var: GlobalVar((self.world() - 1 - j) as u32),
            subst: LocalSubst::id(&self.scopes[self.holes[j].home].cx.gamma),
        }
    }

    /// `t` with the solved holes substituted and the unsolved ones kept, in
    /// the current world.
    fn partial_ty(&self, t: &Type) -> Type {
        let m = self.world() as u32;
        if m == 0 {
            return t.clone();
        }
        t.shift_global_above(m, m).apply_global(&self.sigma(m, |j| self.occurrence(j)))
    }

    fn partial_tm(&self, t: &Term) -> Term {
        let m = self.world() as u32;
        if m == 0 {
            return t.clone();
        }
        t.shift_global_above(m, m).apply_global(&self.sigma(m, |j| self.occurrence(j)))
    }

    /// Scope `s`'s context in the committed world, if no unsolved hole is
    /// in it.
    fn cx(&self, s: usize) -> Result<Cx, Fault> {
        let scope = &self.scopes[s];
        if scope.world == 0 {
            return Ok(scope.cx.clone());
        }
        let gamma = scope.cx.gamma.shift_global((self.world() - scope.world) as u32);
        let a = gamma.apply_global(&self.sigma(0, |_| Term::Zero));
        if a != gamma.apply_global(&self.sigma(0, |_| Term::Succ(Rc::new(Term::Zero)))) {
            return Err(Fault::Ill("a local's type mentions a hole nothing has solved".into()));
        }
        let mut cx = scope.cx.clone();
        cx.gamma = a;
        Ok(cx)
    }

    /// Forget the solutions found after `mark`.
    fn restore(&mut self, mark: usize) {
        if self.trail.len() > mark {
            self.readings.retain(|_, r| r.trail <= mark);
        }
        while self.trail.len() > mark {
            let j = self.trail.pop().expect("a solved hole");
            self.holes[j].sol = None;
        }
    }
}

/// A generated declaration, read back from its generator's run: each
/// parameter's name, implicitness and type (scoped in the parameters before
/// it), the statement and the body under all of them. Everything is in the
/// world the run was in.
pub(crate) struct Member {
    theorem: bool,
    value: bool,
    /// The instance the value is registered as: the class, its type
    /// arguments (in the root scope) and its index arguments by name.
    instance: Option<(String, Vec<(Type, Level)>, Vec<String>)>,
    name: String,
    params: Vec<(String, bool, Type, Level)>,
    result: (Type, Level),
    body: Term,
}

/// One elaborated piece of a returned `Expr`.
#[derive(Clone)]
struct Reified {
    term: Term,
    ty: Type,
    level: Level,
}

/// The state of quoting while one `by`'s tactic expression is elaborated
/// (see the module comment).
pub(crate) struct Quoting {
    /// `tactic::Expr` and its level.
    expr: Type,
    level: Level,
    /// `tactic::host_quote`'s head and type.
    quote: (Term, Rc<Type>),
    /// The goal's context, where every quoted term must live.
    root: LocalCtx,
    /// The quoted terms and types, in handle order after the goal.
    terms: RefCell<Vec<Held>>,
    /// The expression being checked without quoting, by the probe that
    /// decides whether it needs quoting at all.
    plain: Cell<Option<Span>>,
    /// A generator's run issues no goal handle, so its quoted terms are
    /// handles 0 onwards.
    no_goal: bool,
}

impl Elaborator {
    /// `by t` at `goal`: elaborate `t` as a `tactic::Tac<tactic::Expr>`, or
    /// look it up among the registered native tactics, and run it.
    pub(crate) fn run_by(&self, cx: &Cx, tactic: &Expr, goal: &Type, lvl: &Level, span: Span) -> R<Term> {
        let shown = tactic_name(tactic);
        if let heather_syntax::ast::ExprKind::Var(name) = &tactic.kind {
            if self.key_of(name).is_none() && !self.shadowed(cx, name) {
                if let Some(make) = self.policy.native_tactics.borrow().get(name.as_str()) {
                    let mut speaker: Box<dyn NativeTactic> = make();
                    return self.run_tactic(cx, &mut speaker, &shown, goal, lvl, Vec::new(), span);
                }
            }
        }
        let world = self.goal_psi();
        let (closed, quoted) = self.protocol_value(cx, &world, tactic, "host_tag", "by", span)?;
        // One arena for the whole run, which keeps what it forces: each
        // resumed tree is built from closures the earlier ones forced
        // (`ValueArena::cache_tm`).
        let arena = ValueArena::new();
        let reader = Reader::new(&world, &arena);
        let tree = reader.root(closed);
        let mut speaker = Interpreted { elab: self, world: &world, reader, arena: &arena, tree, globals: Default::default() };
        self.run_tactic(cx, &mut speaker, &shown, goal, lvl, quoted, span)
    }

    /// `tactic::name`'s head and type in `world`.
    fn protocol_signature(&self, world: &GlobalCtx, name: &str, keyword: &str, span: Span) -> R<(Term, Type)> {
        let key = format!("tactic::{name}");
        let Some(abs) = self.global_abs(&key) else {
            return err(format!("`{keyword}` runs a value of the `tactic` protocol; add `import tactic;`"), span);
        };
        let len = world.bindings.len();
        let GlobalBinding::Tm { ty, .. } = &world.bindings[abs] else {
            return err(format!("`{key}` is not a term-level global"), span);
        };
        let head = Term::GlobalTm { var: GlobalVar((len - 1 - abs) as u32), subst: LocalSubst::id(&LocalCtx::nil()) };
        Ok((head, ty.shift_global((len - abs) as u32)))
    }

    /// Elaborate `e`, a `by`'s tactic or a `generate`'s generator, at the
    /// type `tactic::entry` takes, with quoting on: a closed term and the
    /// handles its arguments quoted. A generator issues no goal handle, so
    /// its quoted handles start at 0.
    fn protocol_value(&self, cx: &Cx, world: &GlobalCtx, e: &Expr, entry: &str, keyword: &str, span: Span) -> R<(Term, Vec<Held>)> {
        let shown = tactic_name(e);
        let (_, takes) = self.protocol_signature(world, entry, keyword, span)?;
        let Type::Pi { dom_level, dom, .. } = takes else {
            return err(format!("`tactic::{entry}` takes nothing"), span);
        };
        let (quote_head, quote_ty) = self.protocol_signature(world, "host_quote", keyword, span)?;
        let Type::Pi { cod_level, cod, .. } = &quote_ty else {
            return err("`tactic::host_quote` does not take a handle", span);
        };
        let quoting = Rc::new(Quoting {
            expr: (**cod).clone(),
            level: cod_level.clone(),
            quote: (quote_head, Rc::new(quote_ty.clone())),
            root: cx.gamma.clone(),
            terms: RefCell::new(Vec::new()),
            plain: Cell::new(None),
            no_goal: keyword == "generate",
        });
        let term = self.scoped_cell(|s| &s.by_quoting, Some(Rc::clone(&quoting)), || {
            self.elab_check(cx, e, &dom, &dom_level)
        });
        let term = term?;
        let Some(closed) = crate::unification::strengthen_tm(&LocalCtx::nil(), &term, cx.gamma.len() as u32) else {
            return err(
                format!(
                    "`{keyword} {shown}`: its arguments can mention the goal's locals only where it expects an \
                     `Expr`; otherwise it reaches them through the `Goal` request"
                ),
                span,
            );
        };
        let quoted = quoting.terms.borrow().clone();
        Ok((closed, quoted))
    }

    /// While a `by`'s tactic expression is elaborated, `e` at `expected`:
    /// `None` to check it as usual, or a handle to it when `expected` is
    /// `tactic::Expr` and `e` is a term of some other type.
    ///
    /// Checking would not tell the two apart (it defers a mismatch to the
    /// kernel), so `e`'s type is inferred on a clone, with quoting off for
    /// `e` itself but not below it. An `e` whose type cannot be inferred, or
    /// is `Expr`, is checked as usual; anything else is quoted, and must be a
    /// term of the goal's context, not of the tactic expression's own
    /// binders.
    pub(crate) fn quote_for_by(&self, cx: &Cx, e: &Expr, expected: &Type, lvl: &Level) -> R<Option<Term>> {
        let Some(q) = self.scope.by_quoting.borrow().clone() else {
            return Ok(None);
        };
        if q.plain.get() == Some(e.span) {
            q.plain.set(None);
            return Ok(None);
        }
        if !lvl.equiv(&q.level) || !self.conv_types(cx, expected, &q.expr, lvl) {
            return Ok(None);
        }
        // A type's name is quoted as the type (`generate congruences(Tm)`).
        if let heather_syntax::ast::ExprKind::Var(name) = &e.kind
            && !self.shadowed(cx, name)
            && !cx.names.iter_inner().any(|n| n == name)
            && self.lookup_inductive(name).is_some_and(|ind| ind.params.is_empty() && ind.valparams.is_empty())
        {
            let written = heather_syntax::ast::Ty {
                kind: heather_syntax::ast::TyKind::Named { name: name.clone(), args: Vec::new() },
                span: e.span,
            };
            let (ty, level) = self.elab_ty(cx, &written)?;
            let d = (cx.gamma.len() - q.root.len()) as u32;
            let Some(ty) = crate::unification::strengthen_ty(&q.root, &ty, d) else {
                return err("a quoted type must live in the goal's context", e.span);
            };
            return Ok(Some(self.quoted(&q, cx, Held::Type(ty, level), e.span)?));
        }
        // A bare global is quoted as itself, its implicit parameters still
        // binders of its type for `Match` to solve; inferring it would
        // insert them.
        if let heather_syntax::ast::ExprKind::Var(name) = &e.kind
            && !self.shadowed(cx, name)
            && !cx.names.iter_inner().any(|n| n == name)
            && let Some((term, ty, level)) = self.raw_global(name)
            && !(level.equiv(&q.level) && self.conv_types(cx, &ty, &q.expr, &level))
        {
            let root = q.root.len() as u32;
            return Ok(Some(self.quoted(&q, cx, Held::Term(term.shift_local(root), ty.shift_local(root), level), e.span)?));
        }
        q.plain.set(Some(e.span));
        let plain = self.probe(|| {
            let inferred = self.elab_infer(cx, e);
            q.plain.set(None);
            match inferred {
                Err(_) => true,
                Ok((_, ty, level)) => level.equiv(&q.level) && self.conv_types(cx, &ty, &q.expr, &level),
            }
        });
        if plain {
            return Ok(None);
        }
        // Inferred for real, with quoting off: what is quoted is an
        // ordinary term, and its dependencies and notes are this
        // elaborator's.
        let inferred = self.scoped_cell(|s| &s.by_quoting, None, || self.elab_infer(cx, e));
        let (term, ty, level) = inferred?;
        let d = (cx.gamma.len() - q.root.len()) as u32;
        let (Some(term), Some(ty)) = (
            crate::unification::strengthen_tm(&q.root, &term, d),
            crate::unification::strengthen_ty(&q.root, &ty, d),
        ) else {
            return err(
                "this term stands where the tactic expects an `Expr`, so it is quoted, but it mentions a \
                 local of the tactic expression itself; only the goal's locals can be quoted",
                e.span,
            );
        };
        Ok(Some(self.quoted(&q, cx, Held::Term(term, ty, level), e.span)?))
    }

    /// Record a quoted term of the goal's context and return the closed
    /// `host_quote(n)` that stands for it, weakened to `cx`.
    fn quoted(&self, q: &Quoting, cx: &Cx, held: Held, span: Span) -> R<Term> {
        let n = {
            let mut terms = q.terms.borrow_mut();
            terms.push(held);
            terms.len() as u64 - u64::from(q.no_goal)
        };
        let (head, pi) = &q.quote;
        let Type::Pi { dom_level, cod_level, dom, cod } = &**pi else {
            return err("`tactic::host_quote` does not take a handle", span);
        };
        // Built closed, then weakened to `cx` like any closed term.
        let closed = Term::App {
            fun: Rc::new(head.clone()),
            dom_level: dom_level.clone(),
            cod_level: cod_level.clone(),
            dom: Rc::clone(dom),
            cod: Rc::clone(cod),
            arg: Rc::new(crate::inductive::nat_lit(n as usize)),
        };
        Ok(closed.shift_local(cx.gamma.len() as u32))
    }

    /// The host loop: drive `speaker` to a result, answering its requests in
    /// `cx`, and check the result at `goal`. Handle 0 is the goal; `quoted`
    /// are the terms the tactic's arguments quoted, handles 1 onwards.
    #[allow(clippy::too_many_arguments)]
    fn run_tactic(
        &self,
        cx: &Cx,
        speaker: &mut dyn Speaker,
        shown: &str,
        goal: &Type,
        lvl: &Level,
        quoted: Vec<Held>,
        span: Span,
    ) -> R<Term> {
        let fail = |msg: String| err(format!("`by {shown}`: {msg}"), span);
        let mut run = Run::new(cx, span, false);
        run.issue(0, Held::Type(goal.clone(), lvl.clone()));
        run.issue_quoted(quoted);
        self.issue_lets(cx, &mut run);
        match self.drive(&mut run, speaker) {
            Ok(Ended::Result(e)) => {
                let proof = self.finish(&mut run, &e, cx, goal, lvl).or_else(|msg| fail(msg))?;
                // What the run said is reported only now that it succeeded,
                // as one warning: the lints are kept one per span.
                if !run.said.is_empty() {
                    self.emit_lint(crate::Lint::TacticReport, format!("`by {shown}`: {}", run.said.join("\n")), span);
                }
                Ok(proof)
            }
            Ok(Ended::Published(_)) => fail("only `generate` publishes declarations".into()),
            Err(msg) => fail(msg),
        }
    }

    /// The host loop: drive `speaker` until it returns a result or, in a
    /// generator's run, publishes, answering its requests in the run's
    /// scopes. The error is the reason the run stopped.
    fn drive(&self, run: &mut Run, speaker: &mut dyn Speaker) -> Result<Ended, String> {
        let span = run.span;
        let what = if run.generator { "generator" } else { "tactic" };
        let mut step = speaker.start();
        for answered in 0..REQUEST_BUDGET {
            let request = match step {
                Err(msg) => return Err(format!("{msg}, after {answered} requests")),
                Ok(Step::Done(e)) => return Ok(Ended::Result(e)),
                Ok(Step::Ask(request)) => request,
            };
            let answer = match request {
                Request::Goal if run.generator => {
                    return Err("a generator has no goal: `focus` a tactic on a statement it built".into());
                }
                Request::Goal => Answer::Goal(self.goal_view(&run.scopes[0].cx.clone(), run)),
                Request::Defeq(a, b) => Answer::Bool(self.defeq(run, &a, &b).map_err(Fault::msg)?),
                Request::Fail(msg, notes) => {
                    let rendered = self.render_notes(run, &notes).map_err(Fault::msg)?;
                    return Err(format!("the {what} failed: {msg}{rendered}"));
                }
                Request::Infer(e) => Answer::Handle(refusable(self.infer_request(run, &e))?),
                Request::Open(h, name) => Answer::Opened(refusable(self.open_request(run, h, name))?),
                Request::Resolve(name) => Answer::Handle(self.resolve_request(run, &name, span)),
                Request::View(h) => Answer::Head(self.view_request(run, h).map_err(Fault::msg)?),
                Request::Whnf(h) => Answer::Handle(refusable(self.whnf_request(run, h))?),
                Request::Match(ty, target) => Answer::Match(refusable(self.match_request(run, ty, target, span))?),
                Request::Hole(h) => Answer::Handle(refusable(self.hole_request(run, h))?),
                Request::Mark => Answer::Nat(run.trail.len() as u64),
                Request::Restore(mark) => {
                    run.restore(mark as usize);
                    Answer::Unit
                }
                Request::Lookup(name) => Answer::Global(self.lookup_request(run, &name)),
                Request::Cases(e, goal) => Answer::Split(refusable(self.cases_request(run, &e, goal))?),
                Request::Constructor(goal) => Answer::Split(refusable(self.constructor_request(run, goal))?),
                Request::Close(split, proofs) => Answer::Handle(refusable(self.close_request(run, split, &proofs))?),
                Request::Assume(ty, name, under) => Answer::Local(refusable(self.assume_request(run, &ty, name, under))?),
                Request::Ctors(h) => Answer::Ctors(refusable(self.ctors_request(run, h))?),
                Request::AsType(e) => Answer::Handle(refusable(self.as_type_request(run, &e))?),
                Request::Holes(e, n) => Answer::Holes(refusable(self.holes_request(run, &e, n))?),
                Request::Body(g) => Answer::Handle(refusable(self.body_request(run, g))?),
                Request::Arms(h) => Answer::Arms(refusable(self.arms_request(run, h))?),
                Request::Synth(h) => Answer::Handle(refusable(self.synth_request(run, h, span))?),
                Request::Spine(h) => Answer::Spine(refusable(self.spine_request(run, h))?),
                Request::Fields(e) => Answer::Fields(refusable(self.fields_request(run, &e))?),
                Request::Inj(e, k) => Answer::Handle(refusable(self.inj_request(run, &e, k, span))?),
                Request::Absurd(e, goal) => Answer::Handle(refusable(self.absurd_request(run, &e, goal, span))?),
                Request::Say(msg, notes) => {
                    let rendered = self.render_notes(run, &notes).map_err(Fault::msg)?;
                    run.said.push(format!("{msg}{rendered}"));
                    Answer::Unit
                }
                Request::Publish(decls) if run.generator => return Ok(Ended::Published(decls)),
                Request::Publish(_) => return Err("only `generate` publishes declarations; a tactic cannot".into()),
            };
            step = speaker.resume(answer);
        }
        Err(format!("the {what} made more than {REQUEST_BUDGET} requests without finishing"))
    }

    /// The tactic's result as a proof of the goal: elaborated, compared with
    /// the goal (which may solve holes), and in the committed world.
    fn finish(&self, run: &mut Run, e: &RExpr, cx: &Cx, goal: &Type, lvl: &Level) -> Result<Term, String> {
        let r = self.reify(run, e, 0).map_err(|f| format!("the tactic's result is not a term: {}", f.msg()))?;
        let same = r.level.equiv(lvl) && self.same_ty(run, 0, &r.ty, &goal.shift_global(run.world() as u32), lvl).map_err(Fault::msg)?;
        if !same {
            return Err(format!(
                "the tactic returned a proof of `{}`, not of the goal `{}`",
                self.shown_ty(run, 0, &r.ty),
                self.display_type(cx, goal)
            ));
        }
        let proof = run.committed_tm(&r.term).ok_or_else(|| {
            format!("the tactic's proof `{}` mentions a hole nothing solved", self.shown_tm(run, 0, &r.term))
        })?;
        // A `let` the result names is in the proof, which the kernel checks;
        // one only a handle reached may not be, and its block still hands its
        // value to the kernel (`statements::LetValue::discard_around`).
        let mut named = Vec::new();
        e.locals(&mut named);
        for x in named {
            if let Some(l) = run.let_local(x) {
                l.alias.splice(0);
            }
        }
        Ok(proof)
    }

    /// The goal's locals, the most recent first: its binders, and between
    /// them the `let`s each was followed by ([`Self::issue_lets`]).
    fn goal_view(&self, cx: &Cx, run: &mut Run) -> GoalView {
        let n = cx.gamma.len();
        let mut lets: Vec<(usize, LocalView)> = run
            .lets
            .iter()
            .enumerate()
            .rev()
            .map(|(k, l)| (l.alias.depth, LocalView { id: (n + k) as u64, name: l.alias.name.clone(), ty: l.ty }))
            .collect();
        lets.sort_by_key(|(depth, _)| std::cmp::Reverse(*depth));
        let mut lets = lets.into_iter().peekable();
        let mut locals = Vec::with_capacity(n + run.lets.len());
        for i in (0..n).rev() {
            while let Some((_, l)) = lets.next_if(|(depth, _)| *depth > i) {
                locals.push(l);
            }
            let entry = cx.gamma.entries.get(i).expect("a context entry below its length");
            let ty = run.issue(0, Held::Type(entry.ty.shift_local((n - i) as u32), entry.level.clone()));
            locals.push(LocalView { id: i as u64, name: cx.names.get(i).map(str::to_string).unwrap_or_else(|| "_".to_string()), ty });
        }
        locals.extend(lets.map(|(_, l)| l));
        GoalView { target: 0, locals }
    }

    /// Make the `let`s in scope at the goal locals of the run: each one whose
    /// name still means it there (not bound again by a later binder or
    /// `let`) and was written (not one of the elaborator's `#` names). A
    /// `let` is not a kernel binder, since its uses inline its value, but a
    /// fact bound by one is a hypothesis like a parameter is, and a tactic
    /// that searches the goal's locals (`assumption`, `mono`) should find it
    /// without being handed it.
    fn issue_lets(&self, cx: &Cx, run: &mut Run) {
        let n = cx.names.len();
        let aliases: Vec<_> = cx.aliases.iter().collect();
        for (k, alias) in aliases.iter().enumerate() {
            let Some(later) = n.checked_sub(alias.depth) else { continue };
            let shadowed = cx.names.iter_inner().take(later).any(|m| m == alias.name)
                || aliases[k + 1..].iter().any(|b| b.name == alias.name);
            let written = alias.name.chars().next().is_some_and(|c| c.is_alphabetic() || c == '_');
            if shadowed || !written {
                continue;
            }
            // Read, not spliced: whether the value reaches the proof is
            // known only once the tactic has returned one (`finish`).
            let (term, ty) = alias.at((n - alias.depth) as u32);
            let value = run.issue(0, Held::Term(term, ty.clone(), alias.level.clone()));
            let ty = run.issue(0, Held::Type(ty, alias.level.clone()));
            run.lets.push(LetLocal { alias: Rc::clone(alias), value, ty });
        }
    }

    /// `Defeq`: types with types and terms with terms, solving the holes
    /// either side mentions. A failed comparison solves nothing.
    fn defeq(&self, run: &mut Run, a: &RExpr, b: &RExpr) -> Result<bool, Fault> {
        let at = run.join(run.scope_of(a)?, run.scope_of(b)?)?;
        let mark = run.trail.len();
        let same = self.defeq_at(run, at, a, b)?;
        if !same {
            run.restore(mark);
        }
        Ok(same)
    }

    /// [`Self::defeq`] at scope `at`. Reading a side may make holes (a
    /// `Blank`), which grows the world, so the first side is shifted into
    /// the world the second left.
    fn defeq_at(&self, run: &mut Run, at: usize, a: &RExpr, b: &RExpr) -> Result<bool, Fault> {
        let types = a.is_type_form() || b.is_type_form() || self.is_type_handle(run, a)? || self.is_type_handle(run, b)?;
        if types {
            // Types with types; an ill-typed form is no type, equal to nothing.
            let read = |me: &Self, run: &mut Run, e: &RExpr| match me.reify_ty(run, e, at) {
                Ok(t) => Ok(Some(t)),
                Err(Fault::Ill(_)) => Ok(None),
                Err(f) => Err(f),
            };
            let Some((x, lx)) = read(self, run, a)? else { return Ok(false) };
            let m = run.world();
            let Some((y, ly)) = read(self, run, b)? else { return Ok(false) };
            let x = x.shift_global((run.world() - m) as u32);
            return Ok(lx.equiv(&ly) && self.same_ty(run, at, &x, &y, &lx)?);
        }
        let x = match self.reify(run, a, at) {
            Ok(x) => x,
            Err(Fault::Protocol(m)) => return Err(Fault::Protocol(m)),
            Err(Fault::Ill(_)) => return Ok(false),
        };
        let m = run.world();
        let y = match self.reify(run, b, at) {
            Ok(y) => y,
            Err(Fault::Protocol(m)) => return Err(Fault::Protocol(m)),
            Err(Fault::Ill(_)) => return Ok(false),
        };
        let k = (run.world() - m) as u32;
        let x = Reified { term: x.term.shift_global(k), ty: x.ty.shift_global(k), level: x.level };
        self.same_tm(run, at, &x, &y)
    }

    /// Is `e` a handle to a type?
    fn is_type_handle(&self, run: &Run, e: &RExpr) -> Result<bool, Fault> {
        match e {
            RExpr::Hd(h) => Ok(matches!(run.held(*h)?.1, Held::Type(..))),
            _ => Ok(false),
        }
    }

    /// Are two types of the current world the same at scope `at`? Committed
    /// ones are converted as before. One mentioning unsolved holes is
    /// unified against the other, which must not ([`Self::solve`]).
    fn same_ty(&self, run: &mut Run, at: usize, a: &Type, b: &Type, lvl: &Level) -> Result<bool, Fault> {
        let (pa, pb) = (run.partial_ty(a), run.partial_ty(b));
        match (run.committed_ty(&pa), run.committed_ty(&pb)) {
            // A context with an unsolved hole cannot be converted in.
            (Some(x), Some(y)) => Ok(run.cx(at).is_ok_and(|cx| self.conv_types(&cx, &x, &y, lvl))),
            (None, Some(y)) => self.solve(run, at, &pa, &y, lvl),
            (Some(x), None) => self.solve(run, at, &pb, &x, lvl),
            // Two open types are the same when they are the same syntax: a
            // hole applied to a hole of a type that mentions earlier holes
            // (`map: ?A → ?B` after `?A` and `?B`) compares exactly this.
            (None, None) => Ok(pa == pb),
        }
    }

    /// [`Self::same_ty`] for terms: their types, then the terms, compared as
    /// the reflexivity equations they would be the two sides of.
    fn same_tm(&self, run: &mut Run, at: usize, x: &Reified, y: &Reified) -> Result<bool, Fault> {
        if !x.level.equiv(&y.level) || !self.same_ty(run, at, &x.ty, &y.ty, &x.level)? {
            return Ok(false);
        }
        if let (Some(a), Some(b), Some(ty)) = (run.committed_tm(&x.term), run.committed_tm(&y.term), run.committed_ty(&x.ty)) {
            let cx = run.cx(at)?;
            return Ok(self.goal_oracle().convert_term(&cx.gamma, Layer::Prog, &a, &b, &ty, &x.level).is_ok());
        }
        let refl = |r: &Reified| Type::Id {
            level: r.level.clone(),
            ty: Rc::new(r.ty.clone()),
            lhs: Rc::new(r.term.clone()),
            rhs: Rc::new(r.term.clone()),
        };
        if self.same_ty(run, at, &refl(x), &refl(y), &x.level)? {
            return Ok(true);
        }
        // The unifier pairs two rigid spines only when their heads agree, and
        // leaves a side that would unfold to the other "a whnf's to find": a
        // named constant `third()` against `CReal::ofRat(?q)` learns nothing,
        // though `third`'s body is that call. So the committed side is stepped
        // one δ/β reduct at a time, and the comparison retried at each, before
        // it gives up — not its weak head normal form, which would unfold
        // `ofRat` too and leave no call to pair `?q` with.
        let (committed, partial) = match (run.committed_tm(&x.term), run.committed_tm(&y.term)) {
            (Some(a), None) => ((a, x), y),
            (None, Some(b)) => ((b, y), x),
            _ => return Ok(false),
        };
        let (committed, side) = committed;
        let cx = run.cx(at)?;
        let oracle = self.goal_oracle();
        // A reduct is a committed term; the holes are the world's first globals.
        let m = run.world() as u32;
        for reduct in oracle.unfold(&cx.gamma, &committed, Unfold::HoleComparison) {
            let r = Reified { term: reduct.shift_global(m), ty: side.ty.clone(), level: side.level.clone() };
            if self.same_ty(run, at, &refl(&r), &refl(partial), &partial.level)? {
                return Ok(true);
            }
        }
        Ok(false)
    }

    /// Unify `pat`, which mentions unsolved holes, with the committed `subj`
    /// at scope `at`, by the elaborator's own unifier, and keep what it
    /// learned only if `pat` then converts to `subj`.
    ///
    /// The unifier solves a metavariable whose occurrence is the identity of
    /// its context, and a hole made under fewer binders than `at` occurs
    /// weakened. So the holes are unified one home scope at a time, at that
    /// scope, with `at`'s further locals as binders already crossed: a
    /// solution mentioning one of them does not strengthen to the home and
    /// is not learned. The other homes' holes are withheld meanwhile.
    fn solve(&self, run: &mut Run, at: usize, pat: &Type, subj: &Type, lvl: &Level) -> Result<bool, Fault> {
        let m = run.world();
        let mut sols = run.sols();
        let mut homes: Vec<usize> = run
            .holes
            .iter()
            .filter(|h| h.sol.is_none() && run.encloses(h.home, at))
            .map(|h| h.home)
            .collect();
        homes.sort_by_key(|&s| run.len(s));
        homes.dedup();
        for home in homes {
            let Ok(hcx) = run.cx(home) else { continue };
            let mut trial: Vec<Sol> = sols
                .iter()
                .enumerate()
                .map(|(k, s)| match s {
                    Sol::Unsolved if run.holes[m - 1 - k].home != home => Sol::Withheld,
                    other => other.clone(),
                })
                .collect();
            let d = (run.len(at) - run.len(home)) as u32;
            self.unify_under(&hcx, pat, subj, m as u32, d, &mut trial, &[], run.span);
            for (k, t) in trial.into_iter().enumerate() {
                if matches!(sols[k], Sol::Unsolved) && t.solved().is_some() {
                    sols[k] = t;
                }
            }
        }
        let Some(solved) = crate::unification::zonked(pat, m as u32, &sols) else {
            return Ok(false);
        };
        // Kept for the conversion, which happens in `at`'s context as these
        // solutions make it (a local's type may have mentioned a hole).
        let mark = run.trail.len();
        for (k, s) in sols.into_iter().enumerate() {
            let j = m - 1 - k;
            if let (Sol::Solved(t), None) = (s, &run.holes[j].sol) {
                run.holes[j].sol = Some(t);
                run.trail.push(j);
            }
        }
        let same = run.cx(at).is_ok_and(|cx| self.conv_types(&cx, &solved, subj, lvl));
        if !same {
            run.restore(mark);
        }
        Ok(same)
    }

    /// A type of the current world as a message spells it: unsolved holes
    /// are `?1`, `?2`, … in the order they were made.
    fn shown_ty(&self, run: &Run, at: usize, ty: &Type) -> String {
        let Ok(cx) = run.cx(at) else { return "…".to_string() };
        if let Some(t) = run.committed_ty(ty) {
            return self.display_type(&cx, &t);
        }
        let (sigma, names) = self.placeholders(run);
        self.display_rough_type(&cx, &ty.apply_global(&sigma), &names)
    }

    fn shown_tm(&self, run: &Run, at: usize, t: &Term) -> String {
        let Ok(cx) = run.cx(at) else { return "…".to_string() };
        let (sigma, names) = self.placeholders(run);
        self.display_rough_term(&cx, &t.apply_global(&sigma), &names)
    }

    /// The substitution sending each unsolved hole to a display-only global
    /// outside Ψ, and those globals' names.
    fn placeholders(&self, run: &Run) -> (GlobalSubst, Vec<(GlobalVar, String)>) {
        let first = self.placeholder_base();
        let names = (0..run.world()).map(|j| (GlobalVar(first + j as u32), format!("?{}", j + 1))).collect();
        let sigma = run.sigma(0, |j| Term::GlobalTm {
            var: GlobalVar(first + j as u32),
            subst: LocalSubst::id(&run.scopes[run.holes[j].home].cx.gamma),
        });
        (sigma, names)
    }

    /// A failure's notes, one a line, nested by depth; an `At` note's term is
    /// spelled as the diagnostics spell terms.
    fn render_notes(&self, run: &mut Run, notes: &[NoteView]) -> Result<String, Fault> {
        let mut out = String::new();
        for n in notes {
            self.render_note(run, "  ", n, &mut out)?;
        }
        Ok(out)
    }

    fn render_note(&self, run: &mut Run, indent: &str, n: &NoteView, out: &mut String) -> Result<(), Fault> {
        match n {
            NoteView::Tried(what, verdict) => out.push_str(&format!("\n{indent}tried {what}: {verdict}")),
            NoteView::Under(m) => self.render_note(run, &format!("{indent}  "), m, out)?,
            NoteView::At(e, m) => {
                let at = run.scope_of(e)?;
                // A note may be about a type as well as a term.
                let ty = match e {
                    RExpr::Hd(h) => match run.held(*h)? {
                        (s, Held::Type(ty, _)) => Some((s, ty)),
                        _ => None,
                    },
                    _ => None,
                };
                let shown = match ty {
                    Some((s, ty)) => format!("`{}`", self.shown_ty(run, s, &ty)),
                    None => match self.reify(run, e, at) {
                        Ok(r) => format!("`{}`", self.shown_tm(run, at, &r.term)),
                        Err(Fault::Protocol(msg)) => return Err(Fault::Protocol(msg)),
                        Err(Fault::Ill(why)) => format!("an ill-typed term ({why})"),
                    },
                };
                out.push_str(&format!("\n{indent}at {shown}"));
                self.render_note(run, &format!("{indent}  "), m, out)?;
            }
        }
        Ok(())
    }

    fn infer_request(&self, run: &mut Run, e: &RExpr) -> Result<u64, Fault> {
        let at = run.scope_of(e)?;
        let mark = run.trail.len();
        match self.reify(run, e, at) {
            Ok(r) => Ok(run.issue_now(at, Held::Type(run.partial_ty(&r.ty), r.level))),
            Err(f) => {
                run.restore(mark);
                Err(f)
            }
        }
    }

    fn open_request(&self, run: &mut Run, h: u64, name: String) -> Result<OpenedView, Fault> {
        let (at, ty) = match run.held(h)? {
            (s, Held::Type(t, _)) => (s, t),
            (s, Held::Term(t, ty, _)) => return self.open_lam(run, h, s, &t, &ty, name),
        };
        let cx = run.cx(at)?;
        let ty = run.partial_ty(&ty);
        // A committed type is exposed by head normalisation; one with an
        // unsolved hole must already be a function type.
        let (world, pi) = match run.committed_ty(&ty) {
            Some(c) => {
                let w = self
                    .goal_oracle()
                    .whnf_type(&cx.gamma, &c)
                    .map_err(|_| Fault::Ill("ran out of fuel exposing a function type".into()))?;
                (0, w)
            }
            None => (run.world(), ty.clone()),
        };
        let Type::Pi { dom_level, cod_level, dom, cod } = pi else {
            return Err(Fault::Ill(format!("`{}` is not a function type", self.shown_ty(run, at, &ty))));
        };
        let dependent = crate::unification::strengthen_ty(&cx.gamma, &cod, 1).is_none();
        let mut inner = cx.clone();
        inner.gamma = inner.gamma.shift_global(world as u32);
        inner.push(name.clone(), (*dom).clone(), dom_level.clone());
        let id = run.next_id();
        let position = inner.gamma.len() - 1;
        run.scopes.push(Scope { parent: Some(at), cx: inner, world, locals: vec![id] });
        let scope = run.scopes.len() - 1;
        run.opened.push((scope, position));
        let ty = run.issue_in(at, world, Held::Type((*dom).clone(), dom_level));
        let body = run.issue_in(scope, world, Held::Type((*cod).clone(), cod_level));
        Ok(OpenedView { local: LocalView { id, name, ty }, body, dependent })
    }

    /// `Open` of a handle to a λ (a definition's body, a `match` arm): a
    /// local of its domain, and its body under it, as a term at the
    /// codomain of the λ's type.
    fn open_lam(&self, run: &mut Run, h: u64, at: usize, t: &Term, ty: &Type, name: String) -> Result<OpenedView, Fault> {
        let not_lam = || Fault::Ill(format!("handle {h} stands for a term that is not a λ"));
        let t = run.committed_tm(t).ok_or_else(not_lam)?;
        let Term::Lam { dom, dom_level, body, .. } = &t else { return Err(not_lam()) };
        let cx = run.cx(at)?;
        let ty = run.committed_ty(ty).ok_or_else(not_lam)?;
        let pi = self
            .goal_oracle()
            .whnf_type(&cx.gamma, &ty)
            .map_err(|_| Fault::Ill("ran out of fuel exposing a function type".into()))?;
        let Type::Pi { cod, cod_level, .. } = pi else { return Err(not_lam()) };
        let dependent = crate::unification::strengthen_tm(&cx.gamma, body, 1).is_none();
        let mut inner = cx.clone();
        inner.push(name.clone(), (**dom).clone(), dom_level.clone());
        let id = run.next_id();
        let position = inner.gamma.len() - 1;
        run.scopes.push(Scope { parent: Some(at), cx: inner, world: 0, locals: vec![id] });
        let scope = run.scopes.len() - 1;
        run.opened.push((scope, position));
        let ty = run.issue(at, Held::Type((**dom).clone(), dom_level.clone()));
        let body = run.issue(scope, Held::Term((**body).clone(), (*cod).clone(), cod_level));
        Ok(OpenedView { local: LocalView { id, name, ty }, body, dependent })
    }

    /// `Body(g)`: the elaborated value of the definition `g` stands for, at
    /// the root. Only a closed, monomorphic definition with a body has one:
    /// a theorem's proof is discarded once checked and an axiom has none.
    fn body_request(&self, run: &mut Run, g: u64) -> Result<u64, Fault> {
        let key = run.globals.get(g as usize).cloned().ok_or_else(|| Fault::Ill(format!("{g} is not a global this run issued")))?;
        let GlobalKey::At(abs) = key else {
            return Err(Fault::Ill("a type or a kernel former has no body to read".into()));
        };
        let name = self.global_name_at(abs).unwrap_or_else(|| "this global".into());
        let world = self.goal_psi();
        let len = world.bindings.len();
        let Some(GlobalBinding::Tm { ctx, ty, level, body, .. }) = world.bindings.get(abs) else {
            return Err(Fault::Ill(format!("`{name}` is not a term")));
        };
        let Some(body) = body else {
            return Err(Fault::Ill(format!("`{name}` has no body to read: a theorem's proof is not kept, and an axiom has none")));
        };
        if !ctx.entries.is_empty() || matches!(**ty, Type::UPi { .. }) {
            return Err(Fault::Ill(format!("`{name}` is universe-polymorphic or context-dependent, and its body is not read yet")));
        }
        let shift = (len - abs) as u32;
        Ok(run.issue(0, Held::Term(body.shift_global(shift), ty.shift_global(shift), level.clone())))
    }

    /// `Arms(h)`: the `match` `h` stands for, scrutinee and arms. A tier-0
    /// match on a two-constructor inductive (`Bool`) is one kernel `Case`,
    /// its arms the cases under the payload's binder; each is handed out as
    /// a λ over the payload. A `match h:` is that `Case` applied to `refl`,
    /// and the application's argument is listed. Wider matches nest `Case`s
    /// and are refused until a reader needs them.
    fn arms_request(&self, run: &mut Run, h: u64) -> Result<ArmsView, Fault> {
        let (at, held) = run.held(h)?;
        let Held::Term(t, ..) = held else { return Err(Fault::Ill(format!("handle {h} stands for a type, not a match"))) };
        let t = run.committed_tm(&t).ok_or_else(|| Fault::Ill("it mentions a hole nothing has solved".into()))?;
        let mut spine = Vec::new();
        let mut head = &t;
        while let Term::AppAt { fun, arg } = head {
            spine.push(arg);
            head = fun;
        }
        spine.reverse();
        // A `match` on a `Nat` that recurses (a fuel recursion's top match,
        // docs/runtime-fn-setups-design.md §16.11) is the kernel's `Nat`
        // eliminator, applied to the words its motive generalizes (`View`
        // shows that application as `HOther`): `Zero`'s arm is its base as it
        // is (it takes no payload), `Succ`'s a λ over the predecessor and
        // then the recursion's result, and the arguments are the words.
        if let Term::ElimNat { level, motive, base, step, scrut } = head {
            let (sty, slevel) = self.kernel_type(run, at, scrut).ok_or_else(|| Fault::Ill("its scrutinee has no type".into()))?;
            let s = run.issue_shared(at, scrut, sty, slevel);
            let (bty, blevel) = self.kernel_type(run, at, base).ok_or_else(|| Fault::Ill("its `Zero` arm has no type".into()))?;
            let zero = run.issue(at, Held::Term((**base).clone(), bty, blevel));
            let inner = Term::Lam { dom_level: level.clone(), cod_level: level.clone(), dom: Rc::clone(motive), body: Rc::clone(step) };
            let lam = Term::Lam { dom_level: Level::Zero, cod_level: level.clone(), dom: Rc::new(Type::Nat), body: Rc::new(inner) };
            let (aty, alevel) = self.kernel_type(run, at, &lam)
                .ok_or_else(|| Fault::Ill("the `Succ` arm does not type as a function of the predecessor and the recursion".into()))?;
            let succ = run.issue(at, Held::Term(lam, aty, alevel));
            let mut args = Vec::with_capacity(spine.len());
            for a in spine {
                let (aty, alevel) = self.kernel_type(run, at, a).ok_or_else(|| Fault::Ill("an argument has no type".into()))?;
                args.push(run.issue_shared(at, a, aty, alevel));
            }
            return Ok(ArmsView { scrut: s, arms: vec![("Zero".into(), zero), ("Succ".into(), succ)], args });
        }
        let Term::Case { lhs, rhs, lhs_level, rhs_level, motive_level, case_l, case_r, scrut, .. } = head else {
            return Err(Fault::Ill("it is not a `match`".into()));
        };
        let (sty, slevel) = self.kernel_type(run, at, scrut).ok_or_else(|| Fault::Ill("its scrutinee has no type".into()))?;
        let ind = self.display_tag_of(&sty).filter(|ind| ind.ctors.len() == 2)
            .ok_or_else(|| Fault::Ill("only a `match` on a type with two constructors is presented yet".into()))?;
        let s = run.issue_shared(at, scrut, sty, slevel);
        let mut arms = Vec::with_capacity(2);
        for (ctor, (dom, dom_level, case)) in ind.ctors.iter().zip([(lhs, lhs_level, case_l), (rhs, rhs_level, case_r)]) {
            let lam = Term::Lam { dom_level: dom_level.clone(), cod_level: motive_level.clone(), dom: Rc::clone(dom), body: Rc::clone(case) };
            let (aty, alevel) = self.kernel_type(run, at, &lam)
                .ok_or_else(|| Fault::Ill("an arm does not type as a function of its payload".into()))?;
            arms.push((ctor.name.clone(), run.issue(at, Held::Term(lam, aty, alevel))));
        }
        let mut args = Vec::with_capacity(spine.len());
        for a in spine {
            let (aty, alevel) = self.kernel_type(run, at, a).ok_or_else(|| Fault::Ill("an argument has no type".into()))?;
            args.push(run.issue_shared(at, a, aty, alevel));
        }
        Ok(ArmsView { scrut: s, arms, args })
    }

    /// `Spine(h)`: the term `h` stands for as a head applied to arguments,
    /// read off the kernel's applications with nothing reduced but a head β-redex: every
    /// argument, implicit ones included, in order, each with whether the
    /// function's type at it is dependent (its codomain mentions it, as a
    /// type argument's does). A term that is no application is its own head
    /// with no arguments. A subterm the term shares is one handle wherever
    /// it occurs (as for `Arms`), but equal subterms built apart are not:
    /// identity beyond sharing is `Defeq`'s (docs/grind-design.md §3).
    fn spine_request(&self, run: &mut Run, h: u64) -> Result<SpineView, Fault> {
        let (at, held) = run.held(h)?;
        let Held::Term(t, ..) = held else { return Err(Fault::Ill(format!("handle {h} stands for a type, not a term"))) };
        let t = run.committed_tm(&t).ok_or_else(|| Fault::Ill("it mentions a hole nothing has solved".into()))?;
        // A β-redex at the head is read as its contractum, as `View` shows
        // it: an instantiated λ (`(λ s => f(w, s))(x)`, which a `cong_fn` or
        // a lemma's function argument leaves in a type) is the call `f(w, x)`
        // (docs/grind-design.md §14.3).
        let t = Rc::new(crate::spelling::beta_head(&t).unwrap_or(t));
        let mut spine = Vec::new();
        let mut head = &t;
        loop {
            match &**head {
                // A checked application names its codomain; `app@` leaves
                // it to the head's type.
                Term::App { fun, arg, cod, .. } => {
                    spine.push((fun, arg, Some(cod)));
                    head = fun;
                }
                Term::AppAt { fun, arg } => {
                    spine.push((fun, arg, None));
                    head = fun;
                }
                _ => break,
            }
        }
        spine.reverse();
        let cx = run.cx(at)?;
        let mut args = Vec::with_capacity(spine.len());
        for (fun, a, cod) in spine {
            let dependent = match cod {
                Some(cod) => crate::unification::strengthen_ty(&cx.gamma, cod, 1).is_none(),
                None => {
                    let (fty, _) = self.kernel_type(run, at, fun).ok_or_else(|| Fault::Ill("a function in the spine has no type".into()))?;
                    let pi = self
                        .goal_oracle()
                        .whnf_type(&cx.gamma, &fty)
                        .map_err(|_| Fault::Ill("ran out of fuel exposing a function type".into()))?;
                    let Type::Pi { cod, .. } = pi else {
                        return Err(Fault::Ill("a function in the spine is not of a function type".into()));
                    };
                    crate::unification::strengthen_ty(&cx.gamma, &cod, 1).is_none()
                }
            };
            let (aty, alevel) = self.kernel_type(run, at, a).ok_or_else(|| Fault::Ill("an argument has no type".into()))?;
            args.push((run.issue_shared(at, a, aty, alevel), dependent));
        }
        let (hty, hlevel) = self.kernel_type(run, at, head).ok_or_else(|| Fault::Ill("the head has no type".into()))?;
        let head = run.issue_shared(at, head, hty, hlevel);
        Ok(SpineView { head, args })
    }

    /// `Fields(e)`: the term `e`, of a non-indexed inductive type
    /// with one constructor (a record, `∧`), as the type (a reference, as
    /// `Lookup` answers its name) and its fields: each one's name
    /// (its position where it has none) and a handle to its projection, the
    /// term `h.name` elaborates to (`project_field`), at the field's type.
    /// Refused for a type of more constructors or none, codata, an indexed
    /// family, and a type with a field a later field's type mentions (`∃`'s
    /// `witness`): there a field's type is about the value, not a fact of
    /// its own (docs/grind-design.md §12).
    fn fields_request(&self, run: &mut Run, e: &RExpr) -> Result<(u64, Vec<(String, u64)>), Fault> {
        let at = run.scope_of(e)?;
        let mark = run.trail.len();
        let r = self.reify(run, e, at).inspect_err(|_| run.restore(mark))?;
        let unsolved = || Fault::Ill("it mentions a hole nothing has solved".into());
        let (Some(t), Some(ty)) = (run.committed_tm(&r.term), run.committed_ty(&r.ty)) else {
            run.restore(mark);
            return Err(unsolved());
        };
        let t = Rc::new(t);
        let cx = run.cx(at)?;
        // The spelling the inductive is read off is the one projected at,
        // as `inductive_of` reads it: as written, unspelled, or once in head
        // normal form (`a.Same(b)` is a definition whose value is a `∧`).
        let of = |t: &Type| crate::goal_combinators::type_inductive(self, &cx, t);
        let spelled = std::iter::once(Some(ty.clone()))
            .chain(std::iter::once_with(|| self.unspell_here(&ty)))
            .chain(std::iter::once_with(|| self.goal_oracle().whnf_type(&cx.gamma, &ty).ok()))
            .flatten()
            .find_map(|s| of(&s).map(|ind| (ind, s)));
        let Some((ind, record_ty)) = spelled else {
            return Err(Fault::Ill(format!("`{}` is not an inductive type", self.display_type(&cx, &ty))));
        };
        if ind.codata || ind.index.is_some() || ind.ctors.len() != 1 {
            return Err(Fault::Ill(format!("`{}` is not a one-constructor inductive (codata, an indexed family, or {} constructors)", ind.name, ind.ctors.len())));
        }
        let span = run.span;
        let n = ind.ctors[0].fields.len();
        // A field a later one's type mentions is the binder of its `Σ`'s
        // second component; the tag (entry 0) is not a field.
        let mut cur = self.goal_oracle().whnf_type(&cx.gamma, &record_ty).map_err(|_| Fault::Ill("ran out of fuel exposing the record".into()))?;
        for step in 0..=n {
            let Type::Sigma { snd, .. } = cur else { break };
            let Some(rest) = crate::unification::strengthen_ty(&cx.gamma, &snd, 1) else {
                if step == 0 {
                    break;
                }
                let name = ind.ctors[0].fields[step - 1].0.clone().unwrap_or_else(|| format!("{}", step - 1));
                return Err(Fault::Ill(format!("`{}`'s field `{name}` is mentioned by a later field's type", ind.name)));
            };
            cur = self.goal_oracle().whnf_type(&cx.gamma, &rest).map_err(|_| Fault::Ill("ran out of fuel exposing the record".into()))?;
        }
        let mut out = Vec::with_capacity(n);
        for (idx, (name, _)) in ind.ctors[0].fields.iter().enumerate() {
            let (p, pty, plevel) = self
                .project_field(&cx, &ind, &record_ty, Rc::clone(&t), idx, span)
                .map_err(|e| Fault::Ill(format!("field {idx} of `{}`: {}", ind.name, elab_message(e))))?;
            out.push((name.clone().unwrap_or_else(|| format!("{idx}")), run.issue(at, Held::Term(p, pty, plevel))));
        }
        Ok((run.global_ref(GlobalKey::Type(ind.tag)), out))
    }

    /// `Inj(e, k)`: `inj(e, k)`, the equation between the `k`th fields of
    /// the two sides of `e`, a proof of an equation between values of one
    /// constructor (as the sides compute). Refused where the surface `inj`
    /// is: different constructors, a field whose type depends on an earlier
    /// one, a container or a codata child field
    /// (docs/host-elaboration-interface-design.md §25).
    fn inj_request(&self, run: &mut Run, e: &RExpr, k: u64, span: Span) -> Result<u64, Fault> {
        let at = run.scope_of(e)?;
        let mark = run.trail.len();
        let r = self.reify(run, e, at).inspect_err(|_| run.restore(mark))?;
        let (Some(t), Some(ty)) = (run.committed_tm(&r.term), run.committed_ty(&r.ty)) else {
            run.restore(mark);
            return Err(Fault::Ill("it mentions a hole nothing has solved".into()));
        };
        let cx = run.cx(at)?;
        let (p, pty, plevel) = self
            .inj_of_term(&cx, k as usize, t, &ty, span)
            .map_err(|e| Fault::Ill(elab_message(e)))?;
        Ok(run.issue(at, Held::Term(p, pty, plevel)))
    }

    /// `Absurd(e, goal)`: `absurd(e)` at the type `goal` holds, from `e`, a
    /// proof of an equation between values of two different constructors
    /// (as the sides compute). Refused where the surface `absurd` is: one
    /// constructor on both sides, or sides that are no constructors'
    /// (docs/host-elaboration-interface-design.md §25).
    fn absurd_request(&self, run: &mut Run, e: &RExpr, goal: u64, span: Span) -> Result<u64, Fault> {
        let gs = run.held(goal)?.0;
        let at = run.join(run.scope_of(e)?, gs)?;
        let mark = run.trail.len();
        let r = self.reify(run, e, at).inspect_err(|_| run.restore(mark))?;
        // The goal is read after the proof: reifying it may make holes,
        // which a type read before would not be shifted past.
        let (gty, glevel) = match run.held(goal)? {
            (_, Held::Type(t, l)) => (t, l),
            (_, Held::Term(..)) => return Err(Fault::Ill(format!("handle {goal} stands for a term, not a type"))),
        };
        let unsolved = || Fault::Ill("it mentions a hole nothing has solved".into());
        let (Some(t), Some(ty)) = (run.committed_tm(&r.term), run.committed_ty(&r.ty)) else {
            run.restore(mark);
            return Err(unsolved());
        };
        let expected = run.lift(gs, at, |k| gty.shift_local(k))?;
        let expected = run.committed_ty(&expected).ok_or_else(unsolved)?;
        let cx = run.cx(at)?;
        let p = self
            .absurd_of_term(&cx, t, &ty, &expected, &glevel, span)
            .map_err(|e| Fault::Ill(elab_message(e)))?;
        Ok(run.issue(at, Held::Term(p, expected, glevel)))
    }

    /// A name, elaborated where the `by` is. Elaboration may leave notes and
    /// dependencies behind; a failed one is rolled back.
    fn resolve_request(&self, run: &mut Run, name: &str, span: Span) -> Result<u64, String> {
        if !is_name(name) {
            return Err(format!("`{name}` is not a name"));
        }
        let root = &run.scopes[0].cx;
        if !root.names.iter_inner().any(|n| n == name) {
            if let Some((term, ty, level)) = self.raw_global(name) {
                let n = root.gamma.len() as u32;
                return Ok(run.issue(0, Held::Term(term.shift_local(n), ty.shift_local(n), level)));
            }
        }
        let e = Expr { kind: heather_syntax::ast::ExprKind::Var(name.to_string()), span };
        let mark = crate::resolve::SearchMark::of(self);
        match self.elab_infer(&run.scopes[0].cx, &e) {
            Ok((term, ty, level)) => Ok(run.issue(0, Held::Term(term, ty, level))),
            Err(failure) => {
                mark.rollback(self);
                Err(match failure {
                    crate::ElabError::Elab { msg, .. } => msg,
                    _ => format!("`{name}` does not resolve here"),
                })
            }
        }
    }

    /// `Lookup`: the global a name denotes where the `by` is, as an
    /// identity. A type name is looked up as a type first.
    fn lookup_request(&self, run: &mut Run, name: &str) -> Result<u64, String> {
        if !is_name(name) {
            return Err(format!("`{name}` is not a name"));
        }
        let key = match name {
            "Nat" => GlobalKey::Builtin("Nat"),
            "Succ" => GlobalKey::Builtin("Succ"),
            "True" => GlobalKey::Builtin("True"),
            "False" => GlobalKey::Builtin("False"),
            _ => match self.lookup_inductive(name) {
                Some(ind) => GlobalKey::Type(ind.tag),
                None => match self.key_of(name).and_then(|key| self.global_abs(&key)) {
                    Some(abs) => GlobalKey::At(abs),
                    None => return Err(format!("`{name}` names no global here")),
                },
            },
        };
        Ok(run.global_ref(key))
    }

    /// `Hole(ty)`: a new metavariable of the type `ty` stands for, at `ty`'s
    /// scope, as a handle to its occurrence there.
    /// `Holes(e, n)`: `e` applied to `n` new holes, each at its parameter's
    /// type with the holes before it as the earlier arguments. Each prefix
    /// is remembered as a reading ([`Run::readings`]), so the tactic's
    /// `infer` of the application it spells from the holes is a hit, and
    /// the whole costs one exposure and one instantiation per hole (building
    /// the same holes by `infer`, `open` and `hole` re-reads each prefix).
    fn holes_request(&self, run: &mut Run, e: &RExpr, n: u64) -> Result<Vec<u64>, Fault> {
        let at = run.scope_of(e)?;
        let mark = run.trail.len();
        let out = self.holes_at(run, e, n, at);
        if out.is_err() {
            // The holes made before the refusal stay, unsolved and
            // unreachable: the world only grows.
            run.restore(mark);
        }
        out
    }

    fn holes_at(&self, run: &mut Run, e: &RExpr, n: u64, at: usize) -> Result<Vec<u64>, Fault> {
        let r = self.reify(run, e, at)?;
        let m = run.world() as u32;
        let fty = run.partial_ty(&r.ty);
        let mut ty = match run.committed_ty(&fty) {
            Some(c) => self
                .goal_oracle()
                .whnf_type(&run.cx(at)?.gamma, &c)
                .map_err(|_| Fault::Ill("ran out of fuel exposing a function type".into()))?
                .shift_global(m),
            None => fty.clone(),
        };
        // Every hole is made first, so what is built from them is shifted
        // past them once, not once per hole.
        let first = run.world();
        for _ in 0..n {
            run.holes.push(Hole { home: at, sol: None });
        }
        let k = n as u32;
        let mut term = r.term.shift_global(k);
        ty = ty.shift_global(k);
        let mut level = r.level;
        let mut spelled = e.clone();
        let mut out = Vec::with_capacity(n as usize);
        for i in 0..n as usize {
            // Past the first, the type is an instantiated codomain over the
            // new holes, never committed: a parameter must be one outright.
            let Type::Pi { dom_level, cod_level, dom, cod } = ty else {
                return Err(Fault::Ill(format!("`{}` takes fewer than {n} arguments", self.shown_ty(run, at, &fty))));
            };
            let hole = run.occurrence(first + i);
            let h = run.issue_in(at, run.world(), Held::Term(hole.clone(), (*dom).clone(), dom_level.clone()));
            let arg = Rc::new(hole);
            ty = (*cod).clone().apply_local(&LocalSubst::id(&run.scopes[at].cx.gamma).extended(Rc::clone(&arg)));
            term = Term::App { fun: Rc::new(term), dom_level, cod_level: cod_level.clone(), dom, cod, arg };
            level = cod_level;
            spelled = RExpr::App(Box::new(spelled), Box::new(RExpr::Hd(h)));
            let reified = Reified { term: term.clone(), ty: ty.clone(), level: level.clone() };
            let reading = Reading { reified, world: run.world(), trail: run.trail.len() };
            run.readings.insert((at, spelled.clone()), reading);
            out.push(h);
        }
        Ok(out)
    }

    /// `Synth(goal)`: the search a `:= infer` parameter runs, at the type
    /// `goal` stands for, in its scope (docs/facts-on-demand-design.md §4).
    /// This is how a generator asks for a fact and learns that there is
    /// none: the search's failure is a refusal carrying its trace, and a
    /// refused search leaves nothing behind ([`crate::resolve::SearchMark`]).
    /// The type must mention no unsolved hole: the search's trials are the
    /// elaborator's, which know nothing of a run's holes.
    fn synth_request(&self, run: &mut Run, h: u64, span: Span) -> Result<u64, Fault> {
        let unsolved = || Fault::Ill("`Synth` needs a type that mentions no unsolved hole".into());
        let (at, ty, level) = match run.held(h)? {
            (s, Held::Type(t, l)) => (s, run.committed_ty(&t).ok_or_else(unsolved)?, l),
            (_, Held::Term(..)) => return Err(Fault::Ill(format!("handle {h} stands for a term, not a type"))),
        };
        let cx = run.cx(at)?;
        let spelled = self.spell_type_clean(&cx, &ty).unwrap_or_else(|| "the goal".to_string());
        let mark = crate::resolve::SearchMark::of(self);
        let mut trace = Vec::new();
        match self.resolve_goal(&cx, &ty, &level, &spelled, None, span, &mut trace) {
            Some(t) => Ok(run.issue(at, Held::Term(t, ty, level))),
            None => {
                mark.rollback(self);
                Err(Fault::Ill(format!("no evidence for `{spelled}` — the search:{}", crate::resolve::render_trace(&trace))))
            }
        }
    }

    fn hole_request(&self, run: &mut Run, h: u64) -> Result<u64, Fault> {
        let (home, ty, level) = match run.held(h)? {
            (s, Held::Type(t, l)) => (s, run.partial_ty(&t), l),
            (_, Held::Term(..)) => return Err(Fault::Ill(format!("handle {h} stands for a term, not a type"))),
        };
        run.holes.push(Hole { home, sol: None });
        let occurrence = run.occurrence(run.world() - 1);
        Ok(run.issue_in(home, run.world(), Held::Term(occurrence, ty.shift_global(1), level)))
    }

    /// A global term as itself, with its whole type: a lemma's implicit
    /// parameters are ordinary binders of that type, so `Match` can solve
    /// them. `None` for a name that is not a plain top-level term (a local, a
    /// universe-polymorphic or context-dependent declaration). The term and
    /// type are closed.
    pub(crate) fn raw_global(&self, name: &str) -> Option<(Term, Type, Level)> {
        let key = self.key_of(name)?;
        self.raw_global_at(self.global_abs(&key)?)
    }

    /// [`Self::raw_global`] by absolute Ψ index.
    fn raw_global_at(&self, abs: usize) -> Option<(Term, Type, Level)> {
        let world = self.goal_psi();
        let len = world.bindings.len();
        let GlobalBinding::Tm { ctx, ty, level, .. } = world.bindings.get(abs)? else {
            return None;
        };
        if !ctx.entries.is_empty() || matches!(**ty, Type::UPi { .. }) {
            return None;
        }
        let head = Term::GlobalTm { var: GlobalVar((len - 1 - abs) as u32), subst: LocalSubst::id(&LocalCtx::nil()) };
        Some((head, ty.shift_global((len - abs) as u32), level.clone()))
    }

    /// `t`'s type by the kernel's inference, in scope `at`; `t` is committed.
    fn kernel_type(&self, run: &Run, at: usize, t: &Term) -> Option<(Type, Level)> {
        let cx = run.cx(at).ok()?;
        let oracle = self.goal_oracle();
        heather_kernel::typing::infer_term(oracle.world(), 0, Layer::Prog, &cx.gamma, t, self.policy.fuel).ok()
    }

    /// One layer of a handle, read the way the diagnostics read it
    /// (`display.rs`'s recognisers), never reduced. A handle mentioning an
    /// unsolved hole is read from its structure only.
    fn view_request(&self, run: &mut Run, h: u64) -> Result<HeadView, Fault> {
        let (at, held) = run.held(h)?;
        let committed = match &held {
            Held::Type(t, l) => run.committed_ty(t).map(|t| Ok((t, l.clone()))),
            Held::Term(t, ..) => run.committed_tm(t).map(Err),
        };
        if let Some(c) = committed {
            if run.cx(at).is_err() {
                return Ok(HeadView::Other);
            }
            return Ok(match c {
                Ok((ty, level)) => self.view_type(run, at, &ty, &level),
                Err(t) => self.view_term(run, at, &t),
            });
        }
        let m = run.world() as u32;
        Ok(match held {
            Held::Term(t, ..) => match run.partial_tm(&t) {
                Term::GlobalTm { var, .. } if var.0 < m => HeadView::Hole,
                _ => HeadView::Other,
            },
            Held::Type(t, _) => match run.partial_ty(&t) {
                Type::Pi { dom, dom_level, .. } => HeadView::Pi(run.issue_now(at, Held::Type((*dom).clone(), dom_level))),
                Type::Id { level, ty: carrier, lhs, rhs } => {
                    let l = run.issue_now(at, Held::Term((*lhs).clone(), (*carrier).clone(), level.clone()));
                    let r = run.issue_now(at, Held::Term((*rhs).clone(), (*carrier).clone(), level));
                    HeadView::Eq(l, r)
                }
                _ => HeadView::Other,
            },
        })
    }

    fn view_type(&self, run: &mut Run, at: usize, ty: &Type, level: &Level) -> HeadView {
        if let Some(v) = self.view_instance(run, at, ty, level) {
            return v;
        }
        if let Some(inline) = self.unspell_here(ty) {
            return self.view_type(run, at, &inline, level);
        }
        if matches!(ty, Type::Wf { .. } | Type::Sum { .. } | Type::Sigma { .. })
            && let Some(ind) = self.display_tag_of(ty)
        {
            let Some(targs) = self.display_targs(&run.scopes[at].cx, ty, &ind, 0) else {
                return HeadView::Other;
            };
            let args = targs.into_iter().map(|(t, l)| run.issue(at, Held::Type(t, l))).collect();
            return HeadView::Global(run.global_ref(GlobalKey::Type(ind.tag)), ind.name.clone(), args);
        }
        match ty {
            Type::Pi { dom, dom_level, .. } => HeadView::Pi(run.issue(at, Held::Type((**dom).clone(), dom_level.clone()))),
            Type::Id { level, ty: carrier, lhs, rhs } => {
                let l = run.issue(at, Held::Term((**lhs).clone(), (**carrier).clone(), level.clone()));
                let r = run.issue(at, Held::Term((**rhs).clone(), (**carrier).clone(), level.clone()));
                HeadView::Eq(l, r)
            }
            Type::Nat => HeadView::Global(run.global_ref(GlobalKey::Builtin("Nat")), "Nat".into(), Vec::new()),
            Type::Unit { .. } => HeadView::Global(run.global_ref(GlobalKey::Builtin("True")), "True".into(), Vec::new()),
            Type::Empty { .. } => HeadView::Global(run.global_ref(GlobalKey::Builtin("False")), "False".into(), Vec::new()),
            Type::El { tm, .. } => self.view_term(run, at, tm),
            Type::GlobalTy { var, subst } if subst.terms.is_empty() => {
                match self.global_abs_of(*var).and_then(|abs| Some((abs, self.global_name_at(abs)?))) {
                    Some((abs, name)) => HeadView::Global(run.global_ref(GlobalKey::At(abs)), name, Vec::new()),
                    None => HeadView::Other,
                }
            }
            _ => HeadView::Other,
        }
    }

    /// A value-parameterized declaration's instantiation — a class's
    /// dictionary type, `OrderedField<A>(≈, <, <=, +, *)` — as the global and
    /// every argument it is instantiated at, type arguments as types and
    /// value arguments as terms. The arguments are read by unifying `ty` with
    /// the declaration's own template at unknown arguments, `C#tycode_fn`
    /// applied to metavariables and read inline, and the template at what
    /// was solved must convert to `ty`: a type that is not an instance
    /// declines.
    fn view_instance(&self, run: &mut Run, at: usize, ty: &Type, level: &Level) -> Option<HeadView> {
        let ind = self.display_tag_of(ty)?;
        if ind.valparams.is_empty() || ind.index.is_some() {
            return None;
        }
        let cx = run.cx(at).ok()?;
        let m = (ind.params.len() + ind.valparams.len()) as u32;
        let mut code = self.gen_ref(&cx, crate::gendefs::GenDef::TyCodeFn(ind.tag))?.shift_global(m);
        for j in 0..m {
            let meta = Term::GlobalTm { var: GlobalVar(j), subst: LocalSubst::id(&cx.gamma) };
            code = Term::AppAt { fun: Rc::new(code), arg: Rc::new(meta) };
        }
        let template = Type::El { level: level.clone(), tm: Rc::new(code) };
        let inline = self.unspell_here_in(&template, m)?;
        let mut sols = vec![Sol::Unsolved; m as usize];
        self.unify_root(&cx, &inline, ty, m, &mut sols, &[], Span { start: 0, end: 0 });
        let solved = crate::unification::zonked(&inline, m, &sols)?;
        if !self.conv_types(&cx, &solved, ty, level) {
            return None;
        }
        let mut handles = Vec::with_capacity(sols.len());
        for (i, sol) in sols.iter().enumerate() {
            let a = sol.solved()?;
            let (aty, alevel) = self.kernel_type(run, at, a)?;
            handles.push(if i < ind.params.len() {
                let Type::Ty(l) = aty else { return None };
                run.issue(at, Held::Type(Type::El { level: l.clone(), tm: Rc::clone(a) }, l))
            } else {
                run.issue(at, Held::Term((**a).clone(), aty, alevel))
            });
        }
        Some(HeadView::Global(run.global_ref(GlobalKey::Type(ind.tag)), ind.name.clone(), handles))
    }

    /// A field read left inline, `r.name(args…)`, as [`HeadView::Field`].
    fn view_field(&self, run: &mut Run, at: usize, t: &Term) -> Option<HeadView> {
        let (fun, args) = crate::spelling::app_spine(t);
        let (record, name) = self.field_read_parts(&run.scopes[at].cx, fun)?;
        let (rty, rlevel) = self.kernel_type(run, at, record)?;
        let r = run.issue_shared(at, record, rty, rlevel);
        let mut handles = Vec::with_capacity(args.len());
        for a in args {
            let (ty, level) = self.kernel_type(run, at, a)?;
            handles.push(run.issue_shared(at, a, ty, level));
        }
        Some(HeadView::Field(r, name, handles))
    }

    fn view_term(&self, run: &mut Run, at: usize, t: &Term) -> HeadView {
        if let Some(n) = crate::inductive::nat_value(t) {
            return HeadView::Lit(n as u64);
        }
        // `Succ(…)` is what a numeral's weak head normal form is.
        if let Term::Succ(p) = t {
            let p = run.issue(at, Held::Term((**p).clone(), Type::Nat, Level::Zero));
            return HeadView::Global(run.global_ref(GlobalKey::Builtin("Succ")), "Succ".into(), vec![p]);
        }
        // A `match` applied to arguments (a match whose motive is a function
        // type, as a codata observation's is) is stuck on the same scrutinee.
        let mut base = crate::goal_combinators::head_match(t);
        while let Term::AppAt { fun, .. } = base
            && matches!(crate::goal_combinators::head_match(fun), Term::Case { .. } | Term::AppAt { .. })
        {
            base = crate::goal_combinators::head_match(fun);
        }
        if let Term::Case { scrut, .. } | Term::ElimNat { scrut, .. } = base {
            return match self.kernel_type(run, at, scrut) {
                Some((ty, level)) => HeadView::Match(run.issue_shared(at, scrut, ty, level)),
                None => HeadView::Other,
            };
        }
        if let Term::Lam { dom, dom_level, .. } = t {
            return HeadView::Lam(run.issue(at, Held::Type((**dom).clone(), dom_level.clone())));
        }
        if let Some((ind, i, fields)) = self.view_ctor(&run.scopes[at].cx, t) {
            let mut handles = Vec::with_capacity(fields.len());
            for f in &fields {
                let Some((ty, level)) = self.kernel_type(run, at, f) else {
                    return HeadView::Other;
                };
                handles.push(run.issue_shared(at, f, ty, level));
            }
            let name = ind.ctors[i].name.clone();
            return HeadView::Ctor(run.global_ref(GlobalKey::Type(ind.tag)), i as u64, name, handles);
        }
        // A β-redex is shown as its contractum, as the diagnostics spell it:
        // an instantiated λ (a lemma's `f(k)` at `f := λ x => …`) is a call
        // like any other.
        if let Some(r) = crate::spelling::beta_head(t) {
            return self.view_term(run, at, &r);
        }
        let n = run.len(at);
        if let Term::Var(LocalVar(i)) = t {
            return match run.local_at(at, n - 1 - *i as usize) {
                Some(x) => HeadView::Local(x, Vec::new()),
                None => HeadView::Other,
            };
        }
        let Some((head, args)) = self.view_call(&run.scopes[at].cx, t) else {
            return self.view_field(run, at, t).unwrap_or(HeadView::Other);
        };
        let mut handles = Vec::with_capacity(args.len());
        for a in &args {
            let Some((ty, level)) = self.kernel_type(run, at, a) else {
                return HeadView::Other;
            };
            handles.push(run.issue_shared(at, a, ty, level));
        }
        match head {
            crate::display::CallHead::Field(name) | crate::display::CallHead::Global(name, _) => {
                let mut spine = t;
                while let Some((f, _)) = crate::spelling::app_of(spine) {
                    spine = f;
                }
                let Term::GlobalTm { var, .. } = spine else { return HeadView::Other };
                let Some(abs) = self.global_abs_of(*var) else { return HeadView::Other };
                HeadView::Global(run.global_ref(GlobalKey::At(abs)), name, handles)
            }
            crate::display::CallHead::Local(i) => match run.local_at(at, n - 1 - i as usize) {
                Some(x) => HeadView::Local(x, handles),
                None => HeadView::Other,
            },
        }
    }

    fn whnf_request(&self, run: &mut Run, h: u64) -> Result<u64, Fault> {
        let out_of_fuel = |_| Fault::Ill("ran out of fuel reducing it".into());
        let unsolved = || Fault::Ill("it mentions a hole nothing has solved".into());
        let (at, held) = run.held(h)?;
        let gamma = run.cx(at)?.gamma;
        let reduced = match held {
            Held::Type(t, l) => {
                let t = run.committed_ty(&t).ok_or_else(unsolved)?;
                Held::Type(self.goal_oracle().whnf_type(&gamma, &t).map_err(out_of_fuel)?, l)
            }
            Held::Term(t, ty, l) => {
                let (t, ty) = (run.committed_tm(&t).ok_or_else(unsolved)?, run.committed_ty(&ty).ok_or_else(unsolved)?);
                // Projections of a reduct's pairs are read off, as `inj` and
                // `absurd` read a computed side: a constructor value built
                // through the checked spelling is a `View`'s `HCtor` only then.
                let w = self.goal_oracle().whnf_term(&gamma, &t).map_err(out_of_fuel)?;
                Held::Term((*crate::spelling::contract_projections(&Rc::new(w))).clone(), ty, l)
            }
        };
        Ok(run.issue(at, reduced))
    }

    /// `Match(ty, target)`: for k = 0, 1, … leading parameters of `ty`, read
    /// the conclusion with those parameters as metavariables and unify it
    /// with `target` by the elaborator's own unifier (the one implicit
    /// arguments use). The first k whose conclusion, with what was solved
    /// substituted, mentions no unsolved parameter and converts to `target`
    /// is the answer. A solved parameter is a handle to its value; an
    /// unsolved one is left for the caller, who proves it. Nothing here is
    /// trusted: the caller's application is checked like any other `Expr`.
    /// Both must be free of unsolved holes.
    ///
    /// A parameter whose type is a class is filled the way a call's
    /// constraint argument is ([`Self::match_dictionaries`]): from a
    /// dictionary in scope, which also fixes the class's index parameters,
    /// or by resolution once the match has determined its type.
    fn match_request(&self, run: &mut Run, ty: u64, target: u64, span: Span) -> Result<Vec<Option<u64>>, Fault> {
        let unsolved = || Fault::Ill("`Match` needs types that mention no unsolved hole".into());
        let (fs, fty) = match run.held(ty)? {
            (s, Held::Type(t, _)) => (s, run.committed_ty(&t).ok_or_else(unsolved)?),
            (_, Held::Term(..)) => return Err(Fault::Ill(format!("handle {ty} stands for a term, not a type"))),
        };
        let (ts, tty, tlvl) = match run.held(target)? {
            (s, Held::Type(t, l)) => (s, run.committed_ty(&t).ok_or_else(unsolved)?, l),
            (_, Held::Term(..)) => return Err(Fault::Ill(format!("handle {target} stands for a term, not a type"))),
        };
        let at = run.join(fs, ts)?;
        let fty = run.lift(fs, at, |k| fty.shift_local(k))?;
        let tty = run.lift(ts, at, |k| tty.shift_local(k))?;
        let cx = run.cx(at)?;
        let mut inner = cx.clone();
        let shown = fty.clone();
        let mut concl = fty;
        let mut doms: Vec<(Type, Level)> = Vec::new();
        let dicts = MatchDicts::default();
        for _ in 0..=MATCH_PARAMETERS {
            if let Some(sols) = self.match_at(&cx, &concl, &tty, &tlvl, &doms, &dicts, span) {
                let mut slots = Vec::with_capacity(sols.len());
                for sol in sols {
                    slots.push(match sol.and_then(|t| self.kernel_type(run, at, &t).map(|(ty, l)| (t, ty, l))) {
                        Some((t, ty, l)) => Some(run.issue(at, Held::Term(t, ty, l))),
                        None => None,
                    });
                }
                return Ok(slots);
            }
            let pi = match &concl {
                Type::Pi { .. } => concl.clone(),
                _ => match self.goal_oracle().whnf_type(&inner.gamma, &concl) {
                    Ok(w) => w,
                    Err(_) => break,
                },
            };
            let Type::Pi { dom, dom_level, cod, .. } = pi else { break };
            doms.push(((*dom).clone(), dom_level.clone()));
            inner.push("_".into(), (*dom).clone(), dom_level);
            concl = (*cod).clone();
        }
        Err(Fault::Ill(format!(
            "no number of arguments makes the conclusion of `{}` the goal `{}`",
            self.display_type(&cx, &shown),
            self.display_type(&cx, &tty)
        )))
    }

    /// One attempt of [`Self::match_request`]: `concl` is scoped in `cx`
    /// plus the `doms.len()` parameters, which become metavariables `0..k` of
    /// a scratch world over the committed one, as in implicit application.
    /// Tried with the class parameters filled from scope first, and plainly
    /// when that does not match.
    fn match_at(&self, cx: &Cx, concl: &Type, target: &Type, lvl: &Level, doms: &[(Type, Level)], dicts: &MatchDicts, span: Span) -> Option<Vec<Option<Term>>> {
        let k = doms.len();
        if k == 0 {
            return self.conv_types(cx, concl, target, lvl).then(Vec::new);
        }
        let n = k as u32;
        let pat = Self::match_scope(cx, concl, n, n);
        let slot_tys = Self::match_slot_tys(cx, doms, n);
        let attempt = |choice: Option<usize>| -> Result<Vec<Option<Term>>, bool> {
            let mut sols = vec![Sol::Unsolved; k];
            if let Some(c) = choice
                && !self.match_dictionaries(cx, doms, n, &mut sols, dicts, Some(c), span)
            {
                return Err(false);
            }
            self.unify_root(cx, &pat, target, n, &mut sols, &slot_tys, span);
            self.match_dictionaries(cx, doms, n, &mut sols, dicts, None, span);
            let solved = crate::unification::zonked(&pat, n, &sols).ok_or(true)?;
            if !self.conv_types(cx, &solved, target, lvl) {
                return Err(true);
            }
            Ok(sols.iter().map(|s| s.solved().map(|t| (**t).clone())).collect())
        };
        // Each dictionary in scope in turn, until one matches or there is
        // none left to try; then the plain match.
        for c in 0.. {
            match attempt(Some(c)) {
                Ok(sols) => return Some(sols),
                Err(true) => continue,
                Err(false) => break,
            }
        }
        attempt(None).ok()
    }

    /// A match's parameter types over its scratch world, each slot's own
    /// type, which the unifier holds its solution to.
    fn match_slot_tys(cx: &Cx, doms: &[(Type, Level)], n: u32) -> Vec<Type> {
        doms.iter().enumerate().map(|(i, (dom, _))| Self::match_scope(cx, dom, i as u32, n)).collect()
    }

    /// `ty`, scoped in `cx` plus `i` of a match's `n` parameters, over the
    /// scratch world: the parameters are metavariables `0..i`.
    fn match_scope(cx: &Cx, ty: &Type, i: u32, n: u32) -> Type {
        let mut subst = LocalSubst::id(&cx.gamma);
        for j in 0..i {
            subst = subst.extended(Rc::new(Term::GlobalTm { var: GlobalVar(j), subst: LocalSubst::id(&cx.gamma) }));
        }
        ty.shift_global(n).apply_local(&subst)
    }

    /// Fill a match's class parameters as a call fills its constraint
    /// arguments (`docs/operation-indexed-classes-design.md` §5). With a
    /// `choice`, each class parameter is matched against the dictionaries in
    /// scope — the class's own binder or a descendant's, at its carrier, as
    /// the value-slot ladder reads them — which solves the class's carrier
    /// and index parameters, and the parameter is the dictionary resolution
    /// finds there (an upcast from a descendant's binder). The `choice`-th
    /// that fits is taken; `false` when there is none, or no class parameter
    /// at all. Without, a class parameter still unsolved whose type the match
    /// has determined is resolved there, instances included. A wrong guess
    /// costs the attempt and never a wrong term: the conclusion still has to
    /// convert, and the application is checked.
    #[allow(clippy::too_many_arguments)]
    fn match_dictionaries(&self, cx: &Cx, doms: &[(Type, Level)], n: u32, sols: &mut [Sol], dicts: &MatchDicts, choice: Option<usize>, span: Span) -> bool {
        let mut any = false;
        let mut slot_tys: Option<Vec<Type>> = None;
        for (i, (dom, dlvl)) in doms.iter().enumerate() {
            if sols[i].solved().is_some() {
                continue;
            }
            let Some(ind) = dicts.class_at(self, i, dom) else { continue };
            any = true;
            let pat = Self::match_scope(cx, dom, i as u32, n);
            let Some(choice) = choice else {
                if let Some(goal) = crate::unification::zonked(&pat, n, sols)
                    && let Some(dict) = dicts.resolved(self, cx, &goal, dlvl, &ind.name, span)
                {
                    sols[i] = Sol::Solved(Rc::new(dict));
                }
                continue;
            };
            // The candidates are lowered inline, and a lemma's parameter is
            // usually the reference `El (app(C#tycode_fn^δ; ā))`: read it
            // inline too, so the two unify field by field.
            let inline = self.unspell_here_in(&pat, n).unwrap_or_else(|| pat.clone());
            let mut fitting = 0;
            let mut found = false;
            for (goal, glvl) in dicts.goals(self, cx, &ind, span).iter() {
                let mut trial = sols.to_vec();
                let slot_tys = slot_tys.get_or_insert_with(|| Self::match_slot_tys(cx, doms, n));
                self.unify_root(cx, &inline, goal, n, &mut trial, slot_tys, span);
                let fits = crate::unification::zonked(&pat, n, &trial).is_some_and(|z| self.conv_types(cx, &z, goal, glvl));
                if !fits {
                    continue;
                }
                let Some(dict) = dicts.resolved(self, cx, goal, glvl, &ind.name, span) else { continue };
                fitting += 1;
                if fitting <= choice {
                    continue;
                }
                trial[i] = Sol::Solved(Rc::new(dict));
                sols.clone_from_slice(&trial);
                found = true;
                break;
            }
            if !found {
                return false;
            }
        }
        choice.is_none() || any
    }

    /// A returned `Expr` as a term of scope `at` in the current world, built
    /// directly: handles, locals and literals are terms already, an
    /// application is formed against its head's Π after comparing the
    /// argument's type with the domain (which may solve holes), and `Lam`
    /// abstracts an opened local of `at`'s child. No name is resolved and
    /// nothing is re-parsed (design §4.1).
    fn reify(&self, run: &mut Run, e: &RExpr, at: usize) -> Result<Reified, Fault> {
        let m = run.world() as u32;
        match e {
            RExpr::Hd(h) => match run.held(*h)? {
                (s, Held::Type(ty, _)) => Err(Fault::Ill(format!(
                    "handle {h} stands for the type `{}`, which is not a term",
                    self.shown_ty(run, s, &ty)
                ))),
                (s, Held::Term(term, ty, level)) => Ok(Reified {
                    term: run.lift(s, at, |k| term.shift_local(k))?,
                    ty: run.lift(s, at, |k| ty.shift_local(k))?,
                    level,
                }),
            },
            RExpr::Local(x) if run.let_local(*x).is_some() => {
                let value = run.let_local(*x).expect("a `let` local").value;
                self.reify(run, &RExpr::Hd(value), at)
            }
            RExpr::Local(x) => {
                let (s, i) = run.local(*x)?;
                if !run.encloses(s, at) {
                    return Err(Fault::Protocol(format!("local {x} is used outside its binder")));
                }
                let n = run.len(at);
                let (ty, level) = run.local_ty(at, i);
                Ok(Reified { term: Term::Var(LocalVar((n - 1 - i) as u32)), ty, level })
            }
            RExpr::NatLit(k) => Ok(Reified { term: crate::inductive::nat_lit(*k as usize), ty: Type::Nat, level: Level::Zero }),
            RExpr::Global(g) => {
                let key = run.globals.get(*g as usize).cloned().ok_or_else(|| Fault::Protocol(format!("global {g} was not issued by this run")))?;
                let found = match key {
                    GlobalKey::At(abs) => self.raw_global_at(abs),
                    GlobalKey::Type(_) | GlobalKey::Builtin(_) => None,
                };
                let Some((term, ty, level)) = found else {
                    return Err(Fault::Ill(format!("global {g} is a type or a former, not a term")));
                };
                let n = run.len(at) as u32;
                Ok(Reified { term: term.shift_local(n).shift_global(m), ty: ty.shift_local(n).shift_global(m), level })
            }
            RExpr::App(..) if !e.has_blank() => {
                if let Some(r) = run.readings.get(&(at, e.clone())) {
                    let k = (run.world() - r.world) as u32;
                    let r = &r.reified;
                    return Ok(Reified { term: r.term.shift_global(k), ty: r.ty.shift_global(k), level: r.level.clone() });
                }
                let RExpr::App(f, a) = e else { unreachable!() };
                let r = self.reify_app(run, f, a, at)?;
                let reading = Reading { reified: r.clone(), world: run.world(), trail: run.trail.len() };
                run.readings.insert((at, e.clone()), reading);
                Ok(r)
            }
            RExpr::App(f, a) => self.reify_app(run, f, a, at),
            RExpr::Blank => Err(Fault::Ill("`Blank` stands only as an argument".into())),
            RExpr::Pi(..) | RExpr::Equation(..) => Err(Fault::Ill("a `Pi` or an `Equation` stands for a type, not a term".into())),
            RExpr::Lam(x, body) => {
                let (s, i) = run.local(*x)?;
                if run.scopes[s].parent != Some(at) || run.scopes[s].locals.len() != 1 || i < run.len(0) {
                    return Err(Fault::Protocol(format!("`Lam` abstracts local {x}, which is not bound here")));
                }
                let b = self.reify(run, body, s)?;
                let entry = run.scopes[s].cx.gamma.entries.get(i).expect("an opened local");
                let dom = Rc::new(entry.ty.shift_global((run.world() - run.scopes[s].world) as u32));
                let dom_level = entry.level.clone();
                Ok(Reified {
                    term: Term::Lam { dom_level: dom_level.clone(), cod_level: b.level.clone(), dom: Rc::clone(&dom), body: Rc::new(b.term) },
                    ty: Type::Pi { dom_level: dom_level.clone(), cod_level: b.level.clone(), dom, cod: Rc::new(b.ty) },
                    level: Level::join(dom_level, b.level),
                })
            }
        }
    }

    /// `f(a)`, reified at scope `at`.
    fn reify_app(&self, run: &mut Run, f: &RExpr, a: &RExpr, at: usize) -> Result<Reified, Fault> {
        let f = self.reify(run, f, at)?;
        // Reading `f` may have made holes.
        let m = run.world() as u32;
        let fty = run.partial_ty(&f.ty);
        let pi = match run.committed_ty(&fty) {
            Some(c) => self
                .goal_oracle()
                .whnf_type(&run.cx(at)?.gamma, &c)
                .map_err(|_| Fault::Ill("ran out of fuel exposing a function type".into()))?
                .shift_global(m),
            None => fty.clone(),
        };
        let Type::Pi { dom_level, cod_level, dom, cod } = pi else {
            return Err(Fault::Ill(format!("`{}` is applied but is not a function", self.shown_ty(run, at, &fty))));
        };
        let (fun, dom, cod, arg) = if matches!(a, RExpr::Blank) {
            // An argument left to inference: a hole at the domain,
            // at this scope, which the rest of the `Expr` solves.
            run.holes.push(Hole { home: at, sol: None });
            let hole = run.occurrence(run.world() - 1);
            (f.term.shift_global(1), Rc::new(dom.shift_global(1)), Rc::new(cod.shift_global(1)), hole)
        } else {
            let a = self.reify(run, a, at)?;
            let k = run.world() as u32 - m;
            let (fun, dom, cod) = (f.term.shift_global(k), Rc::new(dom.shift_global(k)), Rc::new(cod.shift_global(k)));
            if !a.level.equiv(&dom_level) || !self.same_ty(run, at, &a.ty, &dom, &dom_level)? {
                return Err(Fault::Ill(format!(
                    "an argument of type `{}` where `{}` is expected",
                    self.shown_ty(run, at, &a.ty),
                    self.shown_ty(run, at, &dom)
                )));
            }
            (fun, dom, cod, a.term)
        };
        let arg = Rc::new(arg);
        let ty = (*cod).clone().apply_local(&LocalSubst::id(&run.scopes[at].cx.gamma).extended(Rc::clone(&arg)));
        Ok(Reified {
            term: Term::App { fun: Rc::new(fun), dom_level, cod_level: cod_level.clone(), dom, cod, arg },
            ty,
            level: cod_level,
        })
    }

    /// An `Expr` standing for a type, as a type of scope `at` in the current
    /// world: a type handle, a `Pi` abstracting an introduced local of
    /// `at`'s child, an `Equation` between two terms of one type, or a term
    /// whose type is a universe, decoded.
    fn reify_ty(&self, run: &mut Run, e: &RExpr, at: usize) -> Result<(Type, Level), Fault> {
        match e {
            RExpr::Hd(h) => {
                if let (s, Held::Type(ty, level)) = run.held(*h)? {
                    return Ok((run.lift(s, at, |k| ty.shift_local(k))?, level));
                }
            }
            RExpr::Pi(x, body) => {
                let (s, i) = run.local(*x)?;
                if run.scopes[s].parent != Some(at) || run.scopes[s].locals.len() != 1 || i < run.len(0) {
                    return Err(Fault::Protocol(format!("`Pi` abstracts local {x}, which is not bound here")));
                }
                let (cod, cod_level) = self.reify_ty(run, body, s)?;
                let entry = run.scopes[s].cx.gamma.entries.get(i).expect("an opened local");
                let dom = Rc::new(entry.ty.shift_global((run.world() - run.scopes[s].world) as u32));
                let dom_level = entry.level.clone();
                let level = Level::join(dom_level.clone(), cod_level.clone());
                return Ok((Type::Pi { dom_level, cod_level, dom, cod: Rc::new(cod) }, level));
            }
            RExpr::Equation(l, r) => {
                let l = self.reify(run, l, at)?;
                let m = run.world();
                let r = self.reify(run, r, at)?;
                let k = (run.world() - m) as u32;
                let (lhs, ty) = (l.term.shift_global(k), l.ty.shift_global(k));
                if !l.level.equiv(&r.level) || !self.same_ty(run, at, &r.ty, &ty, &l.level)? {
                    return Err(Fault::Ill(format!(
                        "an equation between a term of `{}` and one of `{}`",
                        self.shown_ty(run, at, &ty),
                        self.shown_ty(run, at, &r.ty)
                    )));
                }
                return Ok((Type::Id { level: l.level.clone(), ty: Rc::new(ty), lhs: Rc::new(lhs), rhs: Rc::new(r.term) }, l.level));
            }
            _ => {}
        }
        // A term whose type is a universe stands for the type it codes.
        let r = self.reify(run, e, at)?;
        let ty = run.partial_ty(&r.ty);
        let universe = match run.committed_ty(&ty) {
            Some(c) => self
                .goal_oracle()
                .whnf_type(&run.cx(at)?.gamma, &c)
                .map_err(|_| Fault::Ill("ran out of fuel reading a type".into()))?,
            None => ty.clone(),
        };
        match universe {
            Type::Ty(level) => Ok((Type::El { level: level.clone(), tm: Rc::new(r.term) }, level)),
            _ => Err(Fault::Ill(format!("a term of `{}` stands where a type is expected", self.shown_ty(run, at, &ty)))),
        }
    }

    /// `AsType(e)`: a handle to the type `e` stands for.
    fn as_type_request(&self, run: &mut Run, e: &RExpr) -> Result<u64, Fault> {
        let at = run.scope_of(e)?;
        let mark = run.trail.len();
        match self.reify_ty(run, e, at) {
            Ok((ty, level)) => Ok(run.issue_now(at, Held::Type(run.partial_ty(&ty), level))),
            Err(f) => {
                run.restore(mark);
                Err(f)
            }
        }
    }

    /// `Assume(ty, name, under)`: a new local of `ty`, in a scope of its own
    /// under `under`'s scope (the root's for `None`), so that `Pi`, `Lam` and
    /// a declaration's parameter list can abstract it.
    fn assume_request(&self, run: &mut Run, ty: &RExpr, name: String, under: Option<u64>) -> Result<LocalView, Fault> {
        let parent = match under {
            None => 0,
            Some(x) if run.let_local(x).is_some() => {
                return Err(Fault::Protocol(format!("local {x} is a `let`, which opens no binder to assume under")));
            }
            Some(x) => run.local(x)?.0,
        };
        let mark = run.trail.len();
        let (t, level) = self.reify_ty(run, ty, parent).inspect_err(|_| run.restore(mark))?;
        let Some(t) = run.committed_ty(&t) else {
            run.restore(mark);
            return Err(Fault::Ill("`Assume` needs a type that mentions no unsolved hole".into()));
        };
        let mut inner = run.cx(parent)?;
        inner.push(name.clone(), t.clone(), level.clone());
        let id = run.next_id();
        let position = inner.gamma.len() - 1;
        run.scopes.push(Scope { parent: Some(parent), cx: inner, world: 0, locals: vec![id] });
        let scope = run.scopes.len() - 1;
        run.opened.push((scope, position));
        let ty = run.issue(parent, Held::Type(t, level));
        Ok(LocalView { id, name, ty })
    }

    /// `Ctors(ty)`: the constructors of the inductive `ty` is, each read off
    /// its own application checked at `ty`, the way `Constructor` reads a
    /// split: the application's fields are markers that record what they are
    /// checked at, twice with different placeholders, and a field whose type
    /// changes between the two mentions an earlier field. Where none does,
    /// the constructor is also built as a function of its fields, by the
    /// same application with the fields its parameters.
    fn ctors_request(&self, run: &mut Run, h: u64) -> Result<Vec<CtorView>, Fault> {
        let (s, ty, lvl) = self.committed_goal(run, h, None, "Ctors")?;
        let cx = run.cx(s)?;
        let Some(ind) = self.inductive_of(&cx, &ty) else {
            return Err(Fault::Ill(format!("`{}` is not an inductive type", self.display_type(&cx, &ty))));
        };
        if ind.codata || ind.index.is_some() {
            return Err(Fault::Ill(format!("`{}` is codata or an indexed family, and `Ctors` reads neither", ind.name)));
        }
        let span = run.span;
        let mut out = Vec::with_capacity(ind.ctors.len());
        for (k, ctor) in ind.ctors.iter().enumerate() {
            let n = ctor.fields.len();
            let app = |args: Vec<Expr>| -> Expr {
                // By the expected type, not by a name the caller's scope
                // might shadow: the anonymous forms where they apply.
                let head = match (ind.ctors.len(), k) {
                    (1, _) => heather_syntax::ANON_CTOR_ONLY.to_string(),
                    (2, 0) => heather_syntax::ANON_CTOR_LEFT.to_string(),
                    (2, _) => heather_syntax::ANON_CTOR_RIGHT.to_string(),
                    _ => format!("{}::{}", ind.name, ctor.name),
                };
                let head = Expr { kind: heather_syntax::ast::ExprKind::Var(head), span };
                if n == 0 && ind.ctors.len() > 2 {
                    return head;
                }
                Expr {
                    kind: heather_syntax::ast::ExprKind::App { head: Box::new(head), args, named: vec![], explicit: false, goal_oriented: false },
                    span,
                }
            };
            let expr = app((0..n).map(|j| leaf_expr(j, span)).collect());
            let skeleton = Skeleton::Constructor(expr);
            let mut runs = Vec::with_capacity(2);
            for placeholder in [Term::Zero, Term::Succ(Rc::new(Term::Zero))] {
                let (built, leaves) =
                    self.probe(|| self.build(&cx, &skeleton, &ty, &lvl, Leaves::Record { placeholder, seen: vec![None; n] }, span));
                built.map_err(|e| Fault::Ill(format!("`{}`: {}", ctor.name, elab_message(e))))?;
                let Leaves::Record { seen, .. } = leaves else { unreachable!("a recording run stays one") };
                runs.push(seen);
            }
            let (second, first) = (runs.pop().expect("two runs"), runs.pop().expect("two runs"));
            let mut fields: Vec<Option<(Type, Level)>> = Vec::with_capacity(n);
            for (a, b) in first.into_iter().zip(second) {
                match (a, b) {
                    (Some((acx, aty, al)), Some((bcx, bty, _))) => {
                        let same = acx.gamma.len() == cx.gamma.len() && acx.gamma == bcx.gamma && aty == bty;
                        fields.push(same.then_some((aty, al)));
                    }
                    _ => return Err(Fault::Ill(format!("a field of `{}` was never elaborated", ctor.name))),
                }
            }
            let function = match fields.iter().cloned().collect::<Option<Vec<_>>>() {
                Some(tys) => Some(self.ctor_function(run, s, &cx, &skeleton, &ty, &lvl, &tys).map_err(|e| {
                    Fault::Ill(format!("`{}` as a function: {e}", ctor.name))
                })?),
                None => None,
            };
            let fields = fields
                .into_iter()
                .zip(&ctor.fields)
                .map(|(f, (name, _))| (name.clone().unwrap_or_default(), f.map(|(t, l)| run.issue(s, Held::Type(t, l)))))
                .collect();
            out.push(CtorView { name: ctor.name.clone(), fields, ctor: function });
        }
        Ok(out)
    }

    /// A constructor as the function `λ x̄. C(x̄)` of its fields, whose types
    /// `tys` mention no earlier field, issued at scope `s`.
    #[allow(clippy::too_many_arguments)]
    fn ctor_function(&self, run: &mut Run, s: usize, cx: &Cx, skeleton: &Skeleton, ty: &Type, lvl: &Level, tys: &[(Type, Level)]) -> Result<u64, String> {
        let n = tys.len();
        let mut inner = cx.clone();
        for (j, (t, l)) in tys.iter().enumerate() {
            let name = crate::goal_combinators::fresh(self, &inner, format!("x{j}"));
            inner.push(name, t.shift_local(j as u32), l.clone());
        }
        let len = inner.gamma.len();
        let fills = (0..n).map(|j| (Term::Var(LocalVar((n - 1 - j) as u32)), len)).collect();
        let search = crate::resolve::SearchMark::of(self);
        let mut term = match self.build(&inner, skeleton, &ty.shift_local(n as u32), lvl, Leaves::Fill(fills), run.span).0 {
            Ok(t) => t,
            Err(e) => {
                search.rollback(self);
                return Err(elab_message(e));
            }
        };
        let mut fty = ty.shift_local(n as u32);
        let mut level = lvl.clone();
        for (j, (t, l)) in tys.iter().enumerate().rev() {
            let dom = Rc::new(t.shift_local(j as u32));
            term = Term::Lam { dom_level: l.clone(), cod_level: level.clone(), dom: Rc::clone(&dom), body: Rc::new(term) };
            fty = Type::Pi { dom_level: l.clone(), cod_level: level.clone(), dom, cod: Rc::new(fty) };
            level = Level::join(l.clone(), level);
        }
        Ok(run.issue(s, Held::Term(term, fty, level)))
    }

    /// A handle's committed type, lifted to scope `to`, for a request that
    /// builds from it.
    fn committed_goal(&self, run: &Run, h: u64, to: Option<usize>, what: &str) -> Result<(usize, Type, Level), Fault> {
        let (s, ty, level) = match run.held(h)? {
            (s, Held::Type(t, l)) => (s, t, l),
            (_, Held::Term(..)) => return Err(Fault::Ill(format!("handle {h} stands for a term, not a type"))),
        };
        let at = to.unwrap_or(s);
        let ty = run.lift(s, at, |k| ty.shift_local(k))?;
        let ty = run.committed_ty(&ty).ok_or_else(|| Fault::Ill(format!("`{what}` needs a goal that mentions no unsolved hole")))?;
        Ok((at, ty, level))
    }

    /// The inductive a type is, reading through its type code (a binder's
    /// domain reached through a definition is `El` of the code) and head
    /// normalisation.
    fn inductive_of(&self, cx: &Cx, ty: &Type) -> Option<Rc<crate::inductive::Inductive>> {
        let of = |t: &Type| crate::goal_combinators::type_inductive(self, cx, t);
        of(ty)
            .or_else(|| of(&self.unspell_here(ty)?))
            .or_else(|| of(&self.goal_oracle().whnf_type(&cx.gamma, ty).ok()?))
    }

    /// `Cases(e, goal)`: split `goal` by the elaborator's own `match` on `e`.
    /// The motive abstracts `e` out of the goal, and with it each position
    /// that reaches `e` only through a definition, as `split_all` does
    /// (`goal_combinators::co_occurrences`): a goal whose two sides match on
    /// the same field behind two definitions is specialised on both.
    fn cases_request(&self, run: &mut Run, e: &RExpr, goal: u64) -> Result<SplitView, Fault> {
        let at = run.join(run.scope_of(e)?, run.held(goal)?.0)?;
        let (_, goal_ty, lvl) = self.committed_goal(run, goal, Some(at), "Cases")?;
        let mark = run.trail.len();
        let r = self.reify(run, e, at).inspect_err(|_| run.restore(mark))?;
        let unsolved = || Fault::Ill("`Cases` needs a scrutinee that mentions no unsolved hole".into());
        let scrut = run.committed_tm(&r.term).ok_or_else(unsolved)?;
        let ty = run.committed_ty(&r.ty).ok_or_else(unsolved)?;
        let cx = run.cx(at)?;
        let Some(ind) = self.inductive_of(&cx, &ty) else {
            return Err(Fault::Ill(format!("its type `{}` is not an inductive type", self.display_type(&cx, &ty))));
        };
        if !ind.flat() || ind.index.is_some() {
            return Err(Fault::Ill(format!(
                "`{}` has a recursive field or an index, and `Cases` splits only types without either",
                ind.name
            )));
        }
        let goal_ty = crate::inductive::decoded(&goal_ty).into_owned();
        let mut pairs = Vec::new();
        let mut budget = 256;
        match &goal_ty {
            Type::Id { lhs, rhs, .. } => {
                for side in [lhs, rhs] {
                    crate::goal_combinators::co_occurrences(self, &cx, side, &scrut, &scrut, &mut budget, &mut pairs);
                }
            }
            Type::El { tm, .. } => {
                for arg in crate::spelling::app_spine(tm).1 {
                    crate::goal_combinators::co_occurrences(self, &cx, arg, &scrut, &scrut, &mut budget, &mut pairs);
                }
            }
            _ => {}
        }
        pairs.push((scrut.clone(), Term::Var(LocalVar(0))));
        // A goal that does not mention `e` is every branch's goal.
        let motive = goal_ty.abstract_local_with_all(&pairs).unwrap_or_else(|| goal_ty.shift_local(1));
        let span = run.span;
        let equation = crate::goal_combinators::fresh(self, &cx, "case".to_string());
        let arms = ind
            .ctors
            .iter()
            .enumerate()
            .map(|(k, ctor)| heather_syntax::Arm {
                ctor: ctor.name.clone(),
                default: false,
                binders: ctor
                    .fields
                    .iter()
                    .enumerate()
                    .map(|(f, (name, _))| heather_syntax::Pat::Var {
                        name: crate::goal_combinators::fresh(self, &cx, name.clone().unwrap_or_else(|| format!("x{f}"))),
                        span,
                    })
                    .collect(),
                body: leaf_expr(k, span),
                span,
            })
            .collect();
        let skeleton = Skeleton::Cases { scrut, ty, level: r.level, motive, equation, arms };
        self.split(run, at, goal_ty, lvl, skeleton, ind.ctors.len())
    }

    /// `Constructor(goal)`: split a goal whose type has one constructor into
    /// its fields, by the anonymous constructor checked at it.
    fn constructor_request(&self, run: &mut Run, goal: u64) -> Result<SplitView, Fault> {
        let (at, goal_ty, lvl) = self.committed_goal(run, goal, None, "Constructor")?;
        let cx = run.cx(at)?;
        let ind = self
            .inductive_of(&cx, &goal_ty)
            .filter(|ind| ind.flat() && ind.index.is_none() && ind.ctors.len() == 1)
            .ok_or_else(|| Fault::Ill(format!("`{}` is not a type with one constructor", self.display_type(&cx, &goal_ty))))?;
        let span = run.span;
        let n = ind.ctors[0].fields.len();
        let expr = Expr {
            kind: heather_syntax::ast::ExprKind::App {
                head: Box::new(Expr { kind: heather_syntax::ast::ExprKind::Var(heather_syntax::ANON_CTOR_ONLY.into()), span }),
                args: (0..n).map(|k| leaf_expr(k, span)).collect(),
                named: vec![],
                explicit: false,
                goal_oriented: false,
            },
            span,
        };
        self.split(run, at, goal_ty, lvl, Skeleton::Constructor(expr), n)
    }

    /// Issue a split of `goal` at scope `at`: elaborate the skeleton with
    /// its `n` leaves recording, and make each leaf a branch scope with a goal.
    ///
    /// The skeleton is elaborated twice, with two different placeholders at
    /// the leaves, and the branches must come out the same: a branch whose
    /// statement mentions another leaf (a dependent field) would otherwise
    /// be stated about a placeholder.
    fn split(&self, run: &mut Run, at: usize, goal: Type, lvl: Level, skeleton: Skeleton, n: usize) -> Result<SplitView, Fault> {
        let cx = run.cx(at)?;
        let mut runs = Vec::with_capacity(2);
        for placeholder in [Term::Zero, Term::Succ(Rc::new(Term::Zero))] {
            let (built, leaves) =
                self.probe(|| self.build(&cx, &skeleton, &goal, &lvl, Leaves::Record { placeholder, seen: vec![None; n] }, run.span));
            built.map_err(|e| Fault::Ill(elab_message(e)))?;
            let Leaves::Record { seen, .. } = leaves else { unreachable!("a recording run stays one") };
            let seen: Option<Vec<_>> = seen.into_iter().collect();
            runs.push(seen.ok_or_else(|| Fault::Ill("a branch of the split was never elaborated".into()))?);
        }
        let (second, first) = (runs.pop().expect("two runs"), runs.pop().expect("two runs"));
        if first.iter().zip(&second).any(|(a, b)| a.0.gamma != b.0.gamma || a.1 != b.1) {
            return Err(Fault::Ill("a branch's statement depends on another branch's proof".into()));
        }
        let base = run.len(at);
        let mut branches = Vec::with_capacity(n);
        let mut views = Vec::with_capacity(n);
        for (bcx, ty, level) in first {
            if bcx.gamma.len() < base {
                return Err(Fault::Protocol("a branch's context does not extend the goal's".into()));
            }
            let scope = run.scopes.len();
            let len = bcx.gamma.len();
            let mut locals = Vec::with_capacity(len - base);
            let mut shown = Vec::with_capacity(len - base);
            for p in base..len {
                let id = run.next_id();
                run.opened.push((scope, p));
                locals.push(id);
                let entry = bcx.gamma.entries.get(p).expect("a context entry below its length");
                let name = bcx.names.get(p).map(str::to_string).unwrap_or_else(|| "_".to_string());
                shown.push((id, name, entry.ty.shift_local((len - p) as u32), entry.level.clone()));
            }
            run.scopes.push(Scope { parent: Some(at), cx: bcx, world: 0, locals });
            let locals = shown
                .into_iter()
                .map(|(id, name, ty, level)| LocalView { id, name, ty: run.issue(scope, Held::Type(ty, level)) })
                .collect();
            let goal = run.issue(scope, Held::Type(ty, level));
            branches.push((scope, goal));
            views.push(BranchView { locals, goal });
        }
        run.splits.push(Rc::new(Split { at, goal, lvl, skeleton, branches }));
        Ok(SplitView { id: (run.splits.len() - 1) as u64, branches: views })
    }

    /// Elaborate a split's skeleton at its goal with its leaves doing what
    /// `leaves` says, and hand back what they did.
    fn build(&self, cx: &Cx, skeleton: &Skeleton, goal: &Type, lvl: &Level, leaves: Leaves, span: Span) -> (R<Term>, Leaves) {
        let state = Rc::new(RefCell::new(leaves));
        let built = self.scoped_cell(|s| &s.host_leaves, Some(Rc::clone(&state)), || match skeleton {
            Skeleton::Cases { scrut, ty, level, motive, equation, arms } => self.elab_convoy(
                cx,
                heather_syntax::MatchForm::Match,
                true,
                equation,
                arms,
                scrut.clone(),
                ty,
                level,
                motive.clone(),
                lvl,
                goal,
                span,
            ),
            Skeleton::Constructor(e) => self.elab_check(cx, e, goal, lvl),
        });
        let leaves = state.borrow().clone();
        (built, leaves)
    }

    /// Leaf `k` of the split being elaborated (see [`Leaves`]).
    pub(crate) fn host_leaf(&self, cx: &Cx, k: usize, expected: &Type, lvl: &Level, span: Span) -> R<Term> {
        let Some(state) = self.scope.host_leaves.borrow().clone() else {
            return err("a tactic's split leaf outside its split", span);
        };
        let mut leaves = state.borrow_mut();
        match &mut *leaves {
            Leaves::Record { placeholder, seen } => {
                if seen.len() <= k {
                    seen.resize(k + 1, None);
                }
                seen[k] = Some((cx.clone(), expected.clone(), lvl.clone()));
                Ok(placeholder.clone())
            }
            Leaves::Fill(proofs) => match proofs.get(k) {
                Some((t, n)) if *n == cx.gamma.len() => Ok(t.clone()),
                _ => err("a split's branch was elaborated in another context than it was proved in", span),
            },
            Leaves::Member { fills, psi } => match fills.get(k) {
                Some((Held::Term(t, ..), n)) if *n == cx.gamma.len() => {
                    Ok(t.shift_global((self.goal_psi().bindings.len() - *psi) as u32))
                }
                _ => err("a generated declaration's body was elaborated in another context than it was built in", span),
            },
        }
    }

    /// The type at a generated declaration's leaf `k` (see [`Leaves`]).
    pub(crate) fn host_ty_leaf(&self, cx: &Cx, k: usize, span: Span) -> R<(Type, Level)> {
        let Some(state) = self.scope.host_leaves.borrow().clone() else {
            return err("a generated declaration's type outside its declaration", span);
        };
        let leaves = state.borrow();
        match &*leaves {
            Leaves::Member { fills, psi } => match fills.get(k) {
                Some((Held::Type(t, l), n)) if *n == cx.gamma.len() => {
                    Ok((t.shift_global((self.goal_psi().bindings.len() - *psi) as u32), l.clone()))
                }
                _ => err("a generated declaration's type was elaborated in another context than it was built in", span),
            },
            _ => err("a generated declaration's type outside its declaration", span),
        }
    }

    /// `generate g(args);`: run the generator `g(args)`, a
    /// `tactic::Tac<List<tactic::Decl>>`, at the module's empty context,
    /// and publish the declarations it ends with, every one of them or none
    /// (design §19).
    ///
    /// Each declaration is built from surface syntax whose parameter types,
    /// statement and body are markers standing for what the generator
    /// built ([`Leaves::Member`]), and elaborated as an ordinary
    /// declaration: its name is checked and registered, its implicit
    /// parameters are the call convention, and the kernel gates it. So a
    /// generated declaration is exactly what the same declaration written in
    /// source would be. The group is one transaction: a member refused
    /// rolls back the ones before it.
    pub(crate) fn elab_generate(&mut self, g: &heather_syntax::ast::GenerateItem) -> R<()> {
        let label = format!("generate {}", tactic_name(&g.generator));
        let (members, psi) = self.run_generator(&g.generator, &label, g.span)?;
        self.publish_members(&members, psi, &label, g.span)
    }

    /// Publish a generator's checked group, every member or none.
    fn publish_members(&mut self, members: &[Member], psi: usize, label: &str, span: Span) -> R<()> {
        self.session_transaction(|me| {
            for m in members {
                me.publish_member(m, psi, span).map_err(|e| match e {
                    crate::ElabError::Elab { msg, span } => crate::ElabError::Elab {
                        msg: format!("`{label}`: the generated `{}` was refused: {msg}", m.name),
                        span,
                    },
                    other => other,
                })?;
            }
            Ok(())
        })
    }

    /// A declaration under a prefix generator, `P(args) fn f …` or
    /// `P(args) def x = e;` (docs/value-definitions-design.md §3). The
    /// generator is called with what the declaration hands it in front of
    /// the written arguments, `P(name, args)` for a `fn` or `theorem` and
    /// `P(name, value, args)` for a `def`, and run as `generate` runs its
    /// generator.
    ///
    /// A `fn` or `theorem` is **consumed**: elaborated and published as
    /// written, then read by the generator (by name, with `lookup`). A `def`
    /// is **rewritten**: the declaration as written is not published; the
    /// generator receives its value (at the type its parameter asks for: a
    /// `String` as data, an `Expr` quoted), and its group must declare the
    /// name. Either way the item is one transaction.
    pub(crate) fn elab_prefixed(&mut self, p: &heather_syntax::ast::PrefixedItem) -> R<()> {
        use heather_syntax::ast::{Block, ExprKind, Stmt, TyKind};
        let d = &p.decl;
        let prefix = match &p.generator.kind {
            ExprKind::Var(n) => n.clone(),
            ExprKind::App { head, .. } => match &head.kind {
                ExprKind::Var(n) => n.clone(),
                _ => unreachable!("the parser writes a prefix as a name or a call of one"),
            },
            _ => unreachable!("the parser writes a prefix as a name or a call of one"),
        };
        let form = if d.value { "def" } else if d.kind == heather_syntax::ast::DeclKind::Theorem { "theorem" } else { "fn" };
        let label = format!("{prefix} {form} {}", d.name);
        if !matches!(self.resolve_name(&prefix), crate::NameRes::Found(_)) {
            return err(
                format!(
                    "`{prefix}` is not a generator in scope: a name before `{form}` is a \
                     generator, a function returning `tactic::Tac<List<tactic::Decl>>` \
                     (docs/value-definitions-design.md §3)"
                ),
                p.generator.span,
            );
        }
        let name = Expr { kind: ExprKind::Str(d.name.clone()), span: d.span };
        let mut handed = vec![name];
        if d.value {
            if !d.tyvars.is_empty() || !d.params.is_empty() {
                return err(
                    format!("`{label}`: a rewritten `def` cannot have type parameters yet"),
                    d.span,
                );
            }
            let value = (*d.body.result).clone();
            // The written type, if any, is the value's: `{ let x: T = e; x }`.
            let value = match &d.result.kind {
                TyKind::TypeOf(_) => value,
                _ => {
                    let local = d.name.rsplit("::").next().unwrap_or(&d.name).to_string();
                    let span = value.span;
                    Expr {
                        kind: ExprKind::Block(Box::new(Block {
                            stmts: vec![Stmt::Let {
                                name: local.clone(),
                                ty: Some(d.result.clone()),
                                expr: value,
                                span,
                                opaque: false,
                            }],
                            result: Box::new(Expr { kind: ExprKind::Var(local), span }),
                            ons: Vec::new(),
                            span,
                        })),
                        span,
                    }
                }
            };
            handed.push(value);
        }
        let generator = match &p.generator.kind {
            ExprKind::App { head, args, named, explicit, goal_oriented } => Expr {
                kind: ExprKind::App {
                    head: head.clone(),
                    args: handed.into_iter().chain(args.iter().cloned()).collect(),
                    named: named.clone(),
                    explicit: *explicit,
                    goal_oriented: *goal_oriented,
                },
                span: p.generator.span,
            },
            _ => Expr {
                kind: ExprKind::App {
                    head: Box::new(p.generator.clone()),
                    args: handed,
                    named: Vec::new(),
                    explicit: false,
                    goal_oriented: false,
                },
                span: p.generator.span,
            },
        };
        self.session_transaction(|me| {
            if !d.value {
                me.elab_decl(d)?;
            }
            // A prefix's call is `P(name, args)` or `P(name, value, args)`,
            // which the refusal says, since the writer did not spell it.
            let convention = if d.value {
                format!("a generator prefixing a `def` is called as `{prefix}(name, value, …)`")
            } else {
                format!("a generator prefixing a `{form}` is called as `{prefix}(name, …)`")
            };
            let (members, psi) = me.run_generator(&generator, &label, p.span).map_err(|e| match e {
                crate::ElabError::Elab { msg, span } if !msg.starts_with(&format!("`{label}`")) => crate::ElabError::Elab {
                    msg: format!("`{label}`: the declaration's call of its generator is refused ({convention}): {msg}"),
                    span,
                },
                crate::ElabError::Elab { msg, span } if msg.contains("the generator's call is ill-typed") => {
                    crate::ElabError::Elab { msg: format!("{msg}; {convention}"), span }
                }
                other => other,
            })?;
            if d.value && !members.iter().any(|m| m.name == d.name) {
                return err(
                    format!(
                        "`{label}`: the generator did not declare `{}`: a generator prefixing a \
                         `def` rewrites it, so its group declares the name",
                        d.name
                    ),
                    p.span,
                );
            }
            me.publish_members(&members, psi, &label, p.span)
        })
    }

    /// Run a generator to its declarations, each read back and checked as
    /// far as the run can (its body against its statement), and the number
    /// of globals of the world they were built in.
    fn run_generator(&self, generator: &Expr, label: &str, span: Span) -> R<(Vec<Member>, usize)> {
        let fail = |msg: String| err(format!("`{label}`: {msg}"), span);
        let cx = Cx::empty();
        let world = self.goal_psi();
        let (closed, quoted) = self.protocol_value(&cx, &world, generator, "host_generator", "generate", span)?;
        let (head, runs) = self.protocol_signature(&world, "host_generator", "generate", span)?;
        let Type::Pi { dom_level, cod_level, dom, cod } = runs else {
            return err("`tactic::host_generator` takes nothing", span);
        };
        // The call is run before anything else reads it, and elaboration
        // leaves a mismatch for the kernel to find, so the kernel checks it
        // first: a value of the wrong type is refused here instead of being
        // evaluated into a stuck answer.
        if let Err(e) = self.kernel_check_term(&world, Layer::Code, &LocalCtx::nil(), &closed, &dom, &dom_level) {
            return fail(format!(
                "the generator's call is ill-typed: it is not a `tactic::Tac<List<tactic::Decl>>` \
                 of these arguments ({e:?})"
            ));
        }
        let tree = Term::App { fun: Rc::new(head), dom_level, cod_level, dom, cod, arg: Rc::new(closed) };
        let arena = ValueArena::new();
        let reader = Reader::new(&world, &arena);
        let tree = reader.root(tree);
        let mut speaker = Interpreted { elab: self, world: &world, reader, arena: &arena, tree, globals: Default::default() };
        let mut run = Run::new(&cx, span, true);
        run.issue_quoted(quoted);
        match self.drive(&mut run, &mut speaker) {
            Ok(Ended::Published(decls)) => {
                let members = decls.iter().map(|d| self.member(&mut run, d)).collect::<Result<Vec<_>, String>>();
                members.map(|m| (m, world.bindings.len())).or_else(fail)
            }
            Ok(Ended::Result(_)) => fail("a generator ends by publishing its declarations".into()),
            Err(msg) => fail(msg),
        }
    }

    /// One published declaration, read back: its parameters must be a
    /// telescope of introduced locals from the root, each in the scope of
    /// the one before, and its body must prove its statement there.
    fn member(&self, run: &mut Run, d: &DeclView) -> Result<Member, String> {
        let name = &d.name;
        if !is_name(name) {
            return Err(format!("`{name}` is not a declaration's name"));
        }
        let at = |why: String| format!("`{name}`: {why}");
        if d.value && !d.params.is_empty() {
            return Err(at("a value (`AsValue`) takes no parameters; a function is `AsFunction`".into()));
        }
        let instance = match &d.instance {
            None => None,
            Some((class, args, index)) => {
                let args = args
                    .iter()
                    .map(|a| self.reify_ty(run, a, 0))
                    .collect::<Result<Vec<_>, Fault>>()
                    .map_err(|f| at(format!("its instance's type argument: {}", f.msg())))?;
                let args = args
                    .into_iter()
                    .map(|(t, l)| run.committed_ty(&t).map(|t| (t, l)))
                    .collect::<Option<Vec<_>>>()
                    .ok_or_else(|| at("its instance's type argument mentions a hole nothing solved".into()))?;
                Some((class.clone(), args, index.clone()))
            }
        };
        let mut parent = 0;
        let mut params = Vec::with_capacity(d.params.len());
        for &(x, implicit) in &d.params {
            if run.let_local(x).is_some() {
                return Err(at(format!("parameter {x} is a `let`, which binds nothing")));
            }
            let (s, i) = run.local(x).map_err(|f| at(f.msg()))?;
            if run.scopes[s].parent != Some(parent) || run.scopes[s].locals.as_slice() != [x] {
                return Err(at(format!("parameter {x} is not introduced under the parameter before it")));
            }
            let cx = run.cx(s).map_err(|f| at(f.msg()))?;
            let entry = cx.gamma.entries.get(i).expect("an introduced local");
            let shown = cx.names.get(i).filter(|n| is_name(n) && !n.contains("::")).map(str::to_string).unwrap_or_else(|| format!("x{}", params.len()));
            params.push((shown, implicit, (*entry.ty).clone(), entry.level.clone()));
            parent = s;
        }
        let (result, level) = self.reify_ty(run, &d.result, parent).map_err(|f| at(format!("its statement: {}", f.msg())))?;
        let m = run.world();
        let body = self.reify(run, &d.body, parent).map_err(|f| at(format!("its body: {}", f.msg())))?;
        let result = result.shift_global((run.world() - m) as u32);
        if !body.level.equiv(&level) || !self.same_ty(run, parent, &body.ty, &result, &level).map_err(|f| at(f.msg()))? {
            return Err(at(format!(
                "its body proves `{}`, not its statement `{}`",
                self.shown_ty(run, parent, &body.ty),
                self.shown_ty(run, parent, &result)
            )));
        }
        let unsolved = |what: &str| at(format!("its {what} mentions a hole nothing solved"));
        let result = run.committed_ty(&result).ok_or_else(|| unsolved("statement"))?;
        let body = run.committed_tm(&body.term).ok_or_else(|| unsolved("body"))?;
        Ok(Member { theorem: d.theorem, value: d.value, instance, name: name.clone(), params, result: (result, level), body })
    }

    /// Elaborate one generated declaration from its skeleton (see
    /// [`Self::elab_generate`]).
    fn publish_member(&mut self, m: &Member, psi: usize, span: Span) -> R<()> {
        use heather_syntax::ast::{Block, Decl, DeclKind, Param, ParamOrigin, Ty, TyKind};
        let n = m.params.len();
        let leaf_ty = |k: usize| Ty { kind: TyKind::Named { name: format!("{LEAF}{k}"), args: Vec::new() }, span };
        let params = m
            .params
            .iter()
            .enumerate()
            .map(|(k, (name, implicit, _, _))| Param {
                name: name.clone(),
                ty: leaf_ty(k),
                implicit: *implicit,
                is_self: false,
                solver: None,
                default: None,
                origin: ParamOrigin::Written,
                symbol: None,
                span,
            })
            .collect();
        let decl = Decl {
            kind: if m.theorem { DeclKind::Theorem } else { DeclKind::Fn },
            is_meta: false,
            is_evidence: false,
            is_interface: false, partial: None,
            value: m.value,
            elaborates: None,
            name: m.name.clone(),
            tyvars: Vec::new(),
            params,
            result: leaf_ty(n),
            decreases: None,
            unfolding: Vec::new(),
            body: Block { stmts: Vec::new(), result: Box::new(leaf_expr(n + 1, span)), ons: Vec::new(), span },
            span,
        };
        let mut fills: Vec<(Held, usize)> =
            m.params.iter().enumerate().map(|(k, (_, _, t, l))| (Held::Type(t.clone(), l.clone()), k)).collect();
        let (result, level) = &m.result;
        fills.push((Held::Type(result.clone(), level.clone()), n));
        fills.push((Held::Term(m.body.clone(), result.clone(), level.clone()), n));
        let state = Rc::new(RefCell::new(Leaves::Member { fills, psi }));
        self.scoped(|s| s.host_leaves.get_mut(), Some(state), |me| me.elab_decl(&decl))?;
        match &m.instance {
            None => Ok(()),
            Some(instance) => self.publish_instance_member(&m.name, instance, psi, span),
        }
    }

    /// An `AsInstance` member, after its value is published: the instance
    /// `class<args…>(index…) { field := name.field, … }`, elaborated as the
    /// same instance written in source (so its key, its coherence and its
    /// index spelling are the ordinary checks). The type arguments are
    /// leaves standing for the types the generator built.
    fn publish_instance_member(
        &mut self,
        name: &str,
        (class, args, index): &(String, Vec<(Type, Level)>, Vec<String>),
        psi: usize,
        span: Span,
    ) -> R<()> {
        use heather_syntax::ast::{ClassRef, ExprKind, InstanceBody, InstanceDecl, InstanceField, Ty, TyKind};
        let Some(info) = self.key_of(class).and_then(|key| self.traits.class(&key).cloned()) else {
            return err(format!("`{name}` is to be an instance of `{class}`, which is not a class in scope"), span);
        };
        let var = |n: &str| Expr { kind: ExprKind::Var(n.to_string()), span };
        let fields = info
            .fields
            .iter()
            .filter_map(|f| f.name.clone())
            .map(|field| InstanceField {
                expr: Expr {
                    kind: ExprKind::Dot { recv: Box::new(var(name)), name: field.clone(), tyargs: Vec::new(), args: None, named: Vec::new() },
                    span,
                },
                name: field,
                span,
            })
            .collect();
        // Each type argument is a leaf standing for the type the generator
        // built, read in the empty context. A function type is spelled as an
        // arrow between two leaves (its codomain read under the binder),
        // because an instance's key reads the carrier's head off its
        // spelling: an arrow is keyed as an arrow (`#Fn`), a leaf by nothing.
        let leaf = |k: usize| Ty { kind: TyKind::Named { name: format!("{LEAF}{k}"), args: Vec::new() }, span };
        let mut fills: Vec<(Held, usize)> = Vec::new();
        let mut spelled = Vec::with_capacity(args.len());
        for (t, l) in args {
            match t {
                Type::Pi { dom_level, cod_level, dom, cod } => {
                    let k = fills.len();
                    fills.push((Held::Type((**dom).clone(), dom_level.clone()), 0));
                    fills.push((Held::Type((**cod).clone(), cod_level.clone()), 1));
                    spelled.push(Ty { kind: TyKind::Fn { binder: None, implicit: false, dom: Box::new(leaf(k)), cod: Box::new(leaf(k + 1)) }, span });
                }
                _ => {
                    spelled.push(leaf(fills.len()));
                    fills.push((Held::Type(t.clone(), l.clone()), 0));
                }
            }
        }
        let decl = InstanceDecl {
            tyvars: Vec::new(),
            valparams: Vec::new(),
            class: ClassRef {
                name: class.clone(),
                args: spelled,
                index: index.iter().map(|n| var(n)).collect(),
                path: Vec::new(),
                span,
            },
            requires: Vec::new(),
            body: InstanceBody::Literal(fields),
            span,
        };
        let state = Rc::new(RefCell::new(Leaves::Member { fills, psi }));
        self.scoped(|s| s.host_leaves.get_mut(), Some(state), |me| me.elab_instance(&decl))
    }

    /// `Close(split, proofs)`: each proof checked at its branch's goal
    /// (which may solve holes), then the skeleton elaborated with them. A
    /// refused close solves nothing.
    fn close_request(&self, run: &mut Run, id: u64, proofs: &[RExpr]) -> Result<u64, Fault> {
        let split = run.splits.get(id as usize).cloned().ok_or_else(|| Fault::Protocol(format!("split {id} was not issued by this run")))?;
        if proofs.len() != split.branches.len() {
            return Err(Fault::Ill(format!(
                "the split has {} branches, and {} proofs were given",
                split.branches.len(),
                proofs.len()
            )));
        }
        let mark = run.trail.len();
        let checked = self.branch_proofs(run, &split, proofs);
        let fills = match checked {
            Ok(fills) => fills,
            Err(f) => {
                run.restore(mark);
                return Err(f);
            }
        };
        let cx = run.cx(split.at)?;
        let search = crate::resolve::SearchMark::of(self);
        match self.build(&cx, &split.skeleton, &split.goal, &split.lvl, Leaves::Fill(fills), run.span).0 {
            Ok(t) => Ok(run.issue(split.at, Held::Term(t, split.goal.clone(), split.lvl.clone()))),
            Err(e) => {
                search.rollback(self);
                run.restore(mark);
                Err(Fault::Ill(elab_message(e)))
            }
        }
    }

    /// Each branch's proof, checked at its goal, in the committed world.
    fn branch_proofs(&self, run: &mut Run, split: &Split, proofs: &[RExpr]) -> Result<Vec<(Term, usize)>, Fault> {
        let mut terms = Vec::with_capacity(proofs.len());
        for (k, (&(scope, goal), p)) in split.branches.iter().zip(proofs).enumerate() {
            let r = self.reify(run, p, scope)?;
            let (_, Held::Type(ty, level)) = run.held(goal)? else { unreachable!("a branch's goal is a type") };
            if !r.level.equiv(&level) || !self.same_ty(run, scope, &r.ty, &ty, &level)? {
                return Err(Fault::Ill(format!(
                    "branch {k}'s proof proves `{}`, not its goal `{}`",
                    self.shown_ty(run, scope, &r.ty),
                    self.shown_ty(run, scope, &ty)
                )));
            }
            terms.push((scope, r.term));
        }
        let mut fills = Vec::with_capacity(terms.len());
        for (k, (scope, t)) in terms.into_iter().enumerate() {
            let c = run.committed_tm(&t).ok_or_else(|| {
                Fault::Ill(format!("branch {k}'s proof `{}` mentions a hole nothing solved", self.shown_tm(run, scope, &t)))
            })?;
            fills.push((c, run.len(scope)));
        }
        Ok(fills)
    }

    /// Make `name` available as `by name` (design §8a). A name a source file
    /// declares, or a local, takes precedence over a native tactic.
    pub fn register_native_tactic(&mut self, name: &str, make: fn() -> Box<dyn NativeTactic>) {
        self.policy.native_tactics.borrow_mut().insert(name.to_string(), make);
    }
}

/// The tactic as its `by` wrote it, for messages.
pub(crate) fn tactic_name(e: &Expr) -> String {
    match &e.kind {
        heather_syntax::ast::ExprKind::Var(name) => name.clone(),
        heather_syntax::ast::ExprKind::App { head, .. } => format!("{}(…)", tactic_name(head)),
        _ => "…".to_string(),
    }
}

/// An elaboration error's message, for a refusal.
fn elab_message(e: crate::ElabError) -> String {
    match e {
        crate::ElabError::Elab { msg, .. } => msg,
        other => format!("{other:?}"),
    }
}

/// Is `name` a possibly qualified identifier?
fn is_name(name: &str) -> bool {
    !name.is_empty()
        && name.split("::").all(|part| {
            let mut cs = part.chars();
            cs.next().is_some_and(|c| c.is_alphabetic() || c == '_') && cs.all(|c| c.is_alphanumeric() || c == '_')
        })
}
