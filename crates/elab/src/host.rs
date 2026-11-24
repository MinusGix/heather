//! The host side of Heather tactics (docs/metaprogramming/host-elaboration-interface-design.md).
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
//! ([`Host::quote_for_by`]). The quoted term is replaced by a closed
//! `host_quote(n)`, so the tactic value stays closed. A term that infers no
//! type (an unannotated `λ`) is quoted as written ([`Quoted::Surface`]) and
//! checked where the tactic's result places it (design §26).
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
//! analyzer path of docs/metaprogramming/analyzer-evaluation-design.md), and an answer is
//! built from the library's builders the same way. Each step is a pending
//! application over the previous tree's closure, so nothing is read back into
//! syntax and re-evaluated, and the force cache shares the tree's spine
//! between steps. The one exception is [`KernelValues::pin`], which looks at
//! a resumed tree's outer pair to keep its proof from chaining.
//!
//! **Which evaluator.** That reading is written once over [`Values`], and a
//! run uses the untrusted machine (`crates/run`, [`MachineValues`]) on a
//! thread of its own, with the kernel's evaluator behind it: where the
//! machine stops, the kernel's is replayed the answers given so far and the
//! run continues there ([`Remote`], [`Host::speak`],
//! docs/infrastructure/untrusted-evaluator-design.md §4). The tree's answers
//! are untrusted either way.

use heather_kernel::rc::Rc;

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
use crate::dispatch::Dictionaries;
use crate::interfaces::InterfaceDefs;
use crate::gendefs::GeneratedDefs;
use crate::inductive::Inductives;
use crate::app_unify::AppUnify;
use crate::inference::Inference;
use crate::traits::ClassesMut;

mod sat;

/// Fuel for **one force** of the tree's value graph — the kernel's own
/// default, deliberately not a bespoke larger one. Each force runs on the
/// **shared** graph, where the bounded cache avoids recent repeated work, so
/// running out is a decline like any other
/// (docs/metaprogramming/analyzer-evaluation-design.md §2).
const READ_FUEL: u64 = heather_kernel::typing::DEFAULT_FUEL;

/// Reads library answers in the kernel's **value domain**: every
/// sub-structure it holds is a [`TmClo`], forced on demand and shared through
/// the arena's cache (docs/metaprogramming/analyzer-evaluation-design.md).
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
    /// What one force may spend.
    fuel: u64,
}

impl<'a, 'v> Reader<'a, 'v> {
    pub(crate) fn new(psi: &'a GlobalCtx, arena: &'v ValueArena<'v>) -> Reader<'a, 'v> {
        Reader { psi, arena, cache: reduce::GlobalCache::for_psi(psi), fuel: READ_FUEL }
    }

    /// A reader whose forces may each spend `fuel`.
    pub(crate) fn with_fuel(psi: &'a GlobalCtx, arena: &'v ValueArena<'v>, fuel: u64) -> Reader<'a, 'v> {
        Reader { fuel, ..Reader::new(psi, arena) }
    }

    /// A two-constructor inductive's value: the constructor's number (0 or
    /// 1), its non-recursive fields and its recursive children, in
    /// declaration order (`List`: `Nil`, and `Cons`'s head and tail).
    pub(crate) fn ctor(&self, c: &'v TmClo<'v>) -> Result<(usize, Vec<&'v TmClo<'v>>, Vec<&'v TmClo<'v>>), String> {
        let w = self.force(c)?;
        let (label, children) = match &*w {
            Val::Supf { label, children, .. } => (*label, self.spine(children)?),
            _ => (self.arena.tm(TmClo::val(w)), vec![]),
        };
        let (index, payload) = match &*self.force(label)? {
            Val::Inl { val, .. } => (0, *val),
            Val::Inr { val, .. } => (1, *val),
            other => return Err(format!("a value that is not a constructor: {other:?}")),
        };
        let Val::Pair { snd, .. } = &*self.force(payload)? else {
            return Err("a constructor whose payload is not a pair".into());
        };
        Ok((index, self.spine(snd)?, children))
    }

    /// The components of a right-nested tuple ending in `⟨⟩`.
    fn spine(&self, c: &'v TmClo<'v>) -> Result<Vec<&'v TmClo<'v>>, String> {
        let mut out = Vec::new();
        let mut v = self.force(c)?;
        loop {
            let next = match &*v {
                Val::Triv { .. } => return Ok(out),
                Val::Pair { fst, snd, .. } => {
                    out.push(*fst);
                    *snd
                }
                _ => return Err("a tuple that is not a chain of pairs".into()),
            };
            v = self.force(next)?;
        }
    }

    /// A `List`'s elements, at most `cap` of them.
    pub(crate) fn list(&self, c: &'v TmClo<'v>, cap: usize) -> Result<Vec<&'v TmClo<'v>>, String> {
        let mut out = Vec::new();
        let mut cell = c;
        loop {
            match self.ctor(cell)? {
                (0, _, _) => return Ok(out),
                (1, fields, children) if fields.len() == 1 && children.len() == 1 => {
                    if out.len() >= cap {
                        return Err(format!("a list longer than {cap}"));
                    }
                    out.push(fields[0]);
                    cell = children[0];
                }
                _ => return Err("a value that is not a list".into()),
            }
        }
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
        let mut ev = Eval::new(self.fuel, Defs::transparent_cached(self.psi, &self.cache), CtxBase::Nil, self.arena);
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

/// A generator's: its requests grow with the declaration it reads (the
/// runtime generator asks about each node of a reflected body and each
/// proof it assembles), so a function of several stores in several arms is
/// past a tactic's budget while still finite.
const GENERATOR_REQUEST_BUDGET: usize = 100_000;

/// Nodes of one returned `Expr`, and characters of one `String`, the host
/// will read before declining (the runaway discipline: the value is produced
/// by library code and may be arbitrarily large). A generator's reply holds
/// the function it compiles, so this is also the largest `runtime fn`: a
/// family of the scanner's automaton (`lib/lang/lexer/lexer_scan.hthr`,
/// about a hundred byte comparisons) is some five thousand nodes
/// (`issues/runtime-generator-program-size.md`).
const READ_BUDGET: usize = 1 << 14;

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
                let Some(index) = Dictionaries(el).scope_index(cx, &ind.name, &carrier, &clvl) else { continue };
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

/// One branch of a split: its new locals, oldest first, its goal, and the
/// fields of the constructor it reaches as the arm binds them (a `Cases` or
/// `Branches` arm's pattern binders, in order; none for `Constructor`). A
/// field is no local: the arm reads it off the constructor's payload, one of
/// the locals (`Inductives::elab_arm`).
#[derive(Clone, Debug)]
pub struct BranchView {
    pub locals: Vec<LocalView>,
    pub goal: u64,
    pub fields: Vec<u64>,
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
    /// `AsRegistered(ty)`: a `def` that is also registered under the type
    /// named `ty`, as `register def` does.
    pub registered: Option<String>,
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
    /// The same, split by a plain `match` (no equation).
    Branches(RExpr, u64),
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
    /// A term's head definition unfolded once at its arguments.
    Unfold(u64),
    /// The representation registered for a type, by the type's handle.
    Repr(u64),
    /// A term's next spelling: its head definition unfolded and the head
    /// reduced on until a call, a local or a value is at the head again.
    Spell(RExpr),
    /// A handle with a local of the goal's context abstracted out of it.
    Abstract(u64, RExpr),
    /// A type handle with a local of the goal's context bound in front.
    Revert(u64, RExpr),
    /// The goal handle closed by simplifying with the laws
    /// (docs/tactics/simp-design.md §7).
    Simp(Vec<RExpr>, u64),
    /// The laws checked as a rewrite system (docs/tactics/simp-design.md §4).
    SimpCheck(Vec<RExpr>),
    /// The numeral a closed term of type `Nat` computes to.
    Numeral(RExpr),
    /// A closed clause list, given to the SAT solver, and how many
    /// variables' values a model reports.
    Sat(RExpr, u64),
    /// A declared global's parameter modes, by its reference.
    Modes(u64),
}

/// The solver's verdict, as `Sat` answers it (`tactic::SatVerdict`): a
/// handle to the refutation, or the model's values of the variables asked
/// about, the lowest first.
#[derive(Clone, Debug)]
pub enum SatView {
    Refuted(u64),
    Model(Vec<bool>),
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
/// of the payload, the arguments the match is applied to, and the fields
/// read off its record, by number, the first read first.
#[derive(Clone, Debug)]
pub struct ArmsView {
    pub scrut: u64,
    pub arms: Vec<(String, u64)>,
    pub args: Vec<u64>,
    pub path: Vec<u64>,
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
    Sat(Result<SatView, String>),
    /// A declared global's parameter modes (`Modes`), in its table's order.
    Modes(Result<Vec<heather_syntax::ParamMode>, String>),
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

/// The protocol from the host's side: the loop in [`Host::run_tactic`]
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

/// What reading the protocol needs of an evaluator: calls of the
/// `tactic::host_*` functions over values it holds, numerals, and a
/// numeral's value. The kernel's evaluator ([`KernelValues`]) and the
/// untrusted one ([`MachineValues`], `crates/run`) both read a tree this
/// way, so the protocol's reading is written once ([`Interpreted`]).
trait Values {
    type V: Copy;
    fn call(&self, name: &'static str, args: Vec<Self::V>) -> Result<Self::V, String>;
    fn lit(&self, n: u64) -> Self::V;
    fn nat(&self, v: Self::V) -> Result<u64, String>;
    /// The tree after a resumption, as the evaluator wants to keep it.
    fn pin(&self, tree: Self::V) -> Result<Self::V, String> {
        Ok(tree)
    }
}

/// A Heather `Tac<Expr>`, read through an evaluator's values.
struct Interpreted<B: Values> {
    values: B,
    tree: B::V,
}

/// The kernel's evaluator, in the value domain over `world`.
struct KernelValues<'a, 'w, 'v> {
    elab: &'a Elaborator,
    world: &'w GlobalCtx,
    reader: Reader<'w, 'v>,
    arena: &'v ValueArena<'v>,
    /// Each `host_*` function's head and rescoped type, looked up once per
    /// run: rescoping a signature is a walk of it, and the loop calls the
    /// same few functions at every step.
    globals: std::cell::RefCell<std::collections::HashMap<&'static str, (Term, Rc<Type>)>>,
}

impl<'a, 'w, 'v> KernelValues<'a, 'w, 'v> {
    /// `tactic::name(args…)` as a pending application over closures. The
    /// `host_*` functions are first-order, so each codomain is used as is.
    fn global(&self, name: &'static str) -> Result<(Term, Rc<Type>), String> {
        if let Some(hit) = self.globals.borrow().get(name) {
            return Ok(hit.clone());
        }
        let key = format!("tactic::{name}");
        let abs = Host(self.elab).protocol_abs(name).ok_or_else(|| {
            format!("`{key}` is not declared; `by` needs the protocol from `import tactic;`")
        })?;
        let GlobalBinding::Tm { ty, .. } = &self.world.bindings[abs] else {
            return Err(format!("`{key}` is not a term-level global"));
        };
        let var = self.world.reference(abs).expect("a binding of the world");
        let empty = LocalCtx::nil();
        let ty = Rc::new(ty.shift_global(var.rescope()));
        let head = Term::GlobalTm {
            var,
            subst: LocalSubst::id(&empty),
        };
        self.globals.borrow_mut().insert(name, (head.clone(), Rc::clone(&ty)));
        Ok((head, ty))
    }

    fn apply(&self, name: &'static str, args: Vec<&'v TmClo<'v>>) -> Result<&'v TmClo<'v>, String> {
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
}

impl<'v> Values for KernelValues<'_, '_, 'v> {
    type V = &'v TmClo<'v>;

    fn call(&self, name: &'static str, args: Vec<&'v TmClo<'v>>) -> Result<&'v TmClo<'v>, String> {
        self.apply(name, args)
    }

    fn lit(&self, n: u64) -> &'v TmClo<'v> {
        self.reader.root(crate::inductive::nat_lit(n as usize))
    }

    fn nat(&self, v: &'v TmClo<'v>) -> Result<u64, String> {
        self.reader.nat(v).map_err(|e| {
            if e.contains("fuel") {
                "evaluating the tactic ran out of fuel or nesting depth".to_string()
            } else {
                e
            }
        })
    }

    /// The tree as a value whose two components are values too.
    ///
    /// `Tac` is tier 2, `Σ(t : W). canon t` (docs/inductives/inductive-tier2-w-lowering.md
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

impl<B: Values> Interpreted<B> {
    fn call(&self, name: &'static str, args: Vec<B::V>) -> Result<B::V, String> {
        self.values.call(name, args)
    }

    fn lit(&self, n: u64) -> B::V {
        self.values.lit(n)
    }

    fn nat_of(&self, name: &'static str, args: Vec<B::V>) -> Result<u64, String> {
        self.values.nat(self.call(name, args)?)
    }

    fn expr(&self, e: B::V, budget: &mut usize) -> Result<RExpr, String> {
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

    fn note(&self, n: B::V, budget: &mut usize) -> Result<NoteView, String> {
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
            let registered = if form == 4 { Some(self.string(self.call("decl_registered_type", vec![d])?)?) } else { None };
            decls.push(DeclView {
                theorem: form == 0,
                value: form == 2 || form == 3 || form == 4,
                instance,
                registered,
                name: self.string(self.call("decl_name", vec![d])?)?,
                params,
                result: self.expr(self.call("decl_result", vec![d])?, &mut budget)?,
                body: self.expr(self.call("decl_body", vec![d])?, &mut budget)?,
            });
        }
        Ok(Request::Publish(decls))
    }

    fn string(&self, s: B::V) -> Result<String, String> {
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

    fn string_value(&self, s: &str) -> Result<B::V, String> {
        let mut out = self.call("str_empty", vec![])?;
        for c in s.chars() {
            out = self.call("str_push", vec![out, self.lit(c as u64)])?;
        }
        Ok(out)
    }

    fn answer(&self, a: &Answer) -> Result<B::V, String> {
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
                    for f in &b.fields {
                        out = self.call("host_branch_field", vec![out, self.lit(*f)])?;
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
                for i in &m.path {
                    out = self.call("host_arms_field", vec![out, self.lit(*i)])?;
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
            Answer::Sat(Ok(SatView::Refuted(h))) => self.call("host_sat_refuted", vec![self.lit(*h)]),
            Answer::Sat(Ok(SatView::Model(bits))) => {
                let mut out = self.call("host_sat_model", vec![])?;
                for b in bits {
                    out = self.call("host_sat_model_next", vec![out, self.lit(*b as u64)])?;
                }
                Ok(out)
            }
            Answer::Sat(Err(why)) => self.call("host_sat_refused", vec![self.string_value(why)?]),
            Answer::Modes(Ok(modes)) => {
                let mut out = self.call("host_modes", vec![])?;
                for m in modes {
                    let code = match m {
                        heather_syntax::ParamMode::Owned => 0,
                        heather_syntax::ParamMode::View => 1,
                        heather_syntax::ParamMode::Path => 2,
                    };
                    out = self.call("host_modes_next", vec![out, self.lit(code)])?;
                }
                Ok(out)
            }
            Answer::Modes(Err(why)) => self.call("host_no_modes", vec![self.string_value(why)?]),
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
            30 => Ok(Step::Ask(Request::Unfold(self.nat_of("host_handle", vec![tree])?))),
            31 => Ok(Step::Ask(Request::Repr(self.nat_of("host_handle", vec![tree])?))),
            32 => {
                let mut budget = READ_BUDGET;
                Ok(Step::Ask(Request::Spell(self.expr(self.call("host_lhs", vec![tree])?, &mut budget)?)))
            }
            33 => {
                let mut budget = READ_BUDGET;
                let x = self.expr(self.call("host_lhs", vec![tree])?, &mut budget)?;
                Ok(Step::Ask(Request::Abstract(self.nat_of("host_handle", vec![tree])?, x)))
            }
            34 => {
                let mut budget = READ_BUDGET;
                let x = self.expr(self.call("host_lhs", vec![tree])?, &mut budget)?;
                Ok(Step::Ask(Request::Revert(self.nat_of("host_handle", vec![tree])?, x)))
            }
            35 => {
                let count = self.nat_of("host_proof_count", vec![tree])?;
                let mut budget = READ_BUDGET;
                let mut laws = Vec::new();
                for i in 0..count {
                    laws.push(self.expr(self.call("host_proof", vec![tree, self.lit(i)])?, &mut budget)?);
                }
                Ok(Step::Ask(Request::Simp(laws, self.nat_of("host_handle", vec![tree])?)))
            }
            36 => {
                let count = self.nat_of("host_proof_count", vec![tree])?;
                let mut budget = READ_BUDGET;
                let mut laws = Vec::new();
                for i in 0..count {
                    laws.push(self.expr(self.call("host_proof", vec![tree, self.lit(i)])?, &mut budget)?);
                }
                Ok(Step::Ask(Request::SimpCheck(laws)))
            }
            37 => {
                let mut budget = READ_BUDGET;
                Ok(Step::Ask(Request::Numeral(self.expr(self.call("host_lhs", vec![tree])?, &mut budget)?)))
            }
            38 => {
                let mut budget = READ_BUDGET;
                let cs = self.expr(self.call("host_lhs", vec![tree])?, &mut budget)?;
                Ok(Step::Ask(Request::Sat(cs, self.nat_of("host_hole_count", vec![tree])?)))
            }
            39 => {
                let mut budget = READ_BUDGET;
                let e = self.expr(self.call("host_lhs", vec![tree])?, &mut budget)?;
                Ok(Step::Ask(Request::Branches(e, self.nat_of("host_handle", vec![tree])?)))
            }
            40 => Ok(Step::Ask(Request::Modes(self.nat_of("host_handle", vec![tree])?))),
            other => Err(format!("a request tree with tag {other}")),
        }
    }
}

impl<B: Values> Speaker for Interpreted<B> {
    fn start(&mut self) -> Result<Step, String> {
        self.step()
    }

    fn resume(&mut self, answer: Answer) -> Result<Step, String> {
        let a = self.answer(&answer)?;
        self.tree = self.values.pin(self.call("host_resume", vec![self.tree, a])?)?;
        self.step()
    }
}

/// What the machine's thread sends the host: the tree's next step, or a
/// protocol function's name to look up (the elaborator stays on its own
/// thread, so the machine asks for each name the first time it calls it).
enum ToHost {
    Step(Result<Step, String>),
    Resolve(&'static str),
}

/// What the host sends the machine's thread.
enum ToMachine {
    Answer(Answer),
    Resolved(Option<usize>),
}

/// The untrusted evaluator (`crates/run`), on its own thread. A value is
/// held by its position in `held` for the run, as the kernel's arena holds
/// what a run forces.
struct MachineValues<'m> {
    machine: &'m heather_run::Machine,
    held: RefCell<Vec<heather_run::Thunk>>,
    globals: RefCell<std::collections::HashMap<&'static str, usize>>,
    to_host: std::sync::mpsc::Sender<ToHost>,
    from_host: std::sync::mpsc::Receiver<ToMachine>,
}

impl MachineValues<'_> {
    fn hold(&self, thunk: heather_run::Thunk) -> usize {
        let mut held = self.held.borrow_mut();
        held.push(thunk);
        held.len() - 1
    }

    fn held(&self, v: usize) -> heather_run::Thunk {
        self.held.borrow()[v].clone()
    }

    fn global(&self, name: &'static str) -> Result<usize, String> {
        if let Some(&at) = self.globals.borrow().get(name) {
            return Ok(at);
        }
        let asked = self.to_host.send(ToHost::Resolve(name)).is_ok();
        let at = match self.from_host.recv() {
            Ok(ToMachine::Resolved(Some(at))) if asked => at,
            _ => return Err(format!("`tactic::{name}` is not declared")),
        };
        self.globals.borrow_mut().insert(name, at);
        Ok(at)
    }
}

impl Values for MachineValues<'_> {
    type V = usize;

    fn call(&self, name: &'static str, args: Vec<usize>) -> Result<usize, String> {
        let mut out = self.machine.global(self.global(name)?);
        for arg in args {
            out = self.machine.apply(&out, &self.held(arg));
        }
        Ok(self.hold(out))
    }

    fn lit(&self, n: u64) -> usize {
        self.hold(self.machine.number(n))
    }

    fn nat(&self, v: usize) -> Result<u64, String> {
        self.machine.nat(&self.held(v)).map_err(|heather_run::Stuck(why)| why)
    }
}

/// The machine's thread: read the tree's steps and resume it with the
/// host's answers until the host hangs up or a step fails.
fn machine_run(machine: &heather_run::Machine, tree: Term, to_host: std::sync::mpsc::Sender<ToHost>, from_host: std::sync::mpsc::Receiver<ToMachine>) {
    let values = MachineValues { machine, held: RefCell::default(), globals: RefCell::default(), to_host, from_host };
    let tree = values.hold(machine.term(tree));
    let mut speaker = Interpreted { values, tree };
    machine.allow(MACHINE_STEP_FUEL);
    let mut step = speaker.start();
    loop {
        let failed = step.is_err();
        if speaker.values.to_host.send(ToHost::Step(step)).is_err() || failed {
            return;
        }
        step = match speaker.values.from_host.recv() {
            Ok(ToMachine::Answer(a)) => {
                machine.allow(MACHINE_STEP_FUEL);
                speaker.resume(a)
            }
            _ => return,
        };
    }
}

/// What the machine may spend producing one step: a runaway's bound, not a
/// verdict, since a step it cannot finish is handed to the kernel's
/// evaluator, whose per-force fuel then decides.
const MACHINE_STEP_FUEL: u64 = 1 << 30;

impl Host<'_> {
    /// `tree`, a closed `Tac` of `world`, run by `with` through a speaker
    /// on the evaluator [`Evaluation::chosen`] names.
    fn speak<T>(&self, world: &GlobalCtx, tree: Term, with: impl FnOnce(&mut dyn Speaker) -> T) -> T {
        // One arena for the whole run, which keeps what it forces: each
        // resumed tree is built from closures the earlier ones forced
        // (`ValueArena::cache_tm`).
        let arena = ValueArena::new();
        let reader = Reader::new(world, &arena);
        let root = reader.root(tree.clone());
        let mut kernel = Interpreted { values: KernelValues { elab: self, world, reader, arena: &arena, globals: Default::default() }, tree: root };
        let how = if self.policy.tactics_on_kernel { Evaluation::Kernel } else { Evaluation::chosen() };
        if how == Evaluation::Kernel {
            return with(&mut kernel);
        }
        let prims = crate::function_ir_source::run_prims(self);
        let (to_machine, from_host) = std::sync::mpsc::channel();
        let (to_host, from_machine) = std::sync::mpsc::channel();
        std::thread::scope(|scope| {
            scope.spawn(move || {
                let failed = to_host.clone();
                let ran = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                    heather_run::with_machine(world, &prims, MACHINE_STEP_FUEL, move |m| machine_run(m, tree, to_host, from_host))
                }));
                let why = match ran {
                    Ok(Ok(())) => return,
                    Ok(Err(heather_run::Stuck(why))) => why,
                    Err(_) => "the machine panicked".to_string(),
                };
                let _ = failed.send(ToHost::Step(Err(why)));
            });
            let mut remote = Remote {
                elab: self,
                to_machine,
                from_machine,
                answers: Vec::new(),
                kernel,
                on_kernel: false,
                check: how == Evaluation::Check,
            };
            let out = with(&mut remote);
            drop(remote);
            out
        })
    }
}

/// How a tactic or generator tree is evaluated (`HEATHER_READS`, as for
/// a compile's reads): on the untrusted machine by default, `kernel` on the
/// kernel's evaluator only, `check` on both in step, refusing a run where
/// they differ.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Evaluation {
    Machine,
    Kernel,
    Check,
}

impl Evaluation {
    fn chosen() -> Evaluation {
        match std::env::var("HEATHER_READS").as_deref() {
            Ok("kernel") => Evaluation::Kernel,
            Ok("check") => Evaluation::Check,
            _ => Evaluation::Machine,
        }
    }
}

/// A tree run on the untrusted machine, with the kernel's evaluator behind
/// it. Nothing the machine answers is trusted any more than the kernel's
/// answer was: every request is the host's to grant, and what a run
/// produces is elaborated and checked. Where the machine fails (a form it
/// does not run, its step or nesting bound), the kernel's evaluator is
/// started on the same tree and handed the answers given so far, which
/// brings it to the same step, and the run goes on there: a failure costs
/// the run again on the kernel's evaluator, never a different outcome.
struct Remote<'h, K: Speaker> {
    elab: &'h Elaborator,
    to_machine: std::sync::mpsc::Sender<ToMachine>,
    from_machine: std::sync::mpsc::Receiver<ToHost>,
    answers: Vec<Answer>,
    kernel: K,
    /// The machine failed and the kernel's evaluator has taken over.
    on_kernel: bool,
    /// `Check`: the kernel's evaluator runs in step and each step is compared.
    check: bool,
}

impl<K: Speaker> Remote<'_, K> {
    /// The machine's next step, or the kernel's from where the machine
    /// stopped.
    fn next(&mut self) -> Result<Step, String> {
        let why = loop {
            match self.from_machine.recv() {
                Ok(ToHost::Resolve(name)) => {
                    let _ = self.to_machine.send(ToMachine::Resolved(Host(self.elab).protocol_abs(name)));
                }
                Ok(ToHost::Step(Ok(step))) => return Ok(step),
                Ok(ToHost::Step(Err(why))) => break why,
                Err(_) => break "the machine's thread ended".to_string(),
            }
        };
        self.fallback(why)
    }

    /// The kernel's evaluator, brought to the machine's step by the answers
    /// given so far. In `check`, where it already runs in step, the
    /// machine's failure is the run's.
    fn fallback(&mut self, why: String) -> Result<Step, String> {
        if std::env::var_os("HEATHER_READ_TRACE").is_some() {
            eprintln!("tactic run: left to the kernel's evaluator after {} answers ({why})", self.answers.len());
        }
        self.on_kernel = true;
        if self.check {
            return Err(format!("the untrusted evaluator stopped where the kernel's did not ({why})"));
        }
        let mut step = self.kernel.start();
        for a in std::mem::take(&mut self.answers) {
            step?;
            step = self.kernel.resume(a);
        }
        step
    }

    /// The machine's step, compared with the kernel's in `check`.
    fn checked(&mut self, machine: Result<Step, String>, kernel: impl FnOnce(&mut K) -> Result<Step, String>) -> Result<Step, String> {
        if !self.check || self.on_kernel {
            return machine;
        }
        let machine = machine?;
        let kernel = kernel(&mut self.kernel)?;
        if format!("{machine:?}") != format!("{kernel:?}") {
            return Err(format!("the untrusted evaluator and the kernel's disagree on a step: {machine:?} against {kernel:?}"));
        }
        Ok(machine)
    }
}

impl<K: Speaker> Speaker for Remote<'_, K> {
    fn start(&mut self) -> Result<Step, String> {
        let machine = self.next();
        self.checked(machine, |k| k.start())
    }

    fn resume(&mut self, answer: Answer) -> Result<Step, String> {
        if self.on_kernel {
            return self.kernel.resume(answer);
        }
        if !self.check {
            self.answers.push(answer.clone());
        }
        let machine = match self.to_machine.send(ToMachine::Answer(answer.clone())) {
            Ok(()) => self.next(),
            Err(_) => self.fallback("the machine's thread ended".into()),
        };
        self.checked(machine, |k| k.resume(answer))
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
    /// The substitutions over every hole, built once per state of the holes
    /// ([`HoleSubsts`]); every change to `holes` goes through
    /// [`Run::add_hole`] or [`Run::set_solution`], which drop them.
    substs: RefCell<HoleSubsts>,
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
    /// (docs/native/runtime-fn-setups-design.md §3.2). The `Rc` held here keeps the
    /// address from being reused while the run lasts.
    shared: std::collections::HashMap<(usize, usize), (Rc<Term>, u64)>,
    /// What the run said (`Say`), reported at its span once it succeeds.
    said: Vec<String>,
    /// The surface terms the arguments quoted, by handle ([`Quoted`]).
    surfaces: std::collections::HashMap<u64, Expr>,
    /// The first surface term that failed to check, reported as itself if
    /// the run fails.
    surface_error: Option<crate::ElabError>,
}

/// [`Run::sigma`]'s three substitutions, each built the first time it is
/// asked for after the holes last changed. `partial_ty` is asked for at
/// every application node a reading meets, and the committed tests twice
/// per declaration and request; each built its substitution afresh, a copy
/// (and for `partial_ty` a shift) of every solved hole's solution, so a
/// reading cost its nodes times the run's holes
/// (issues/runtime-generator-link-cost.md, 2026-11-12 and 2026-11-18).
#[derive(Default)]
struct HoleSubsts {
    /// Solutions shifted past the world, unsolved holes as their occurrences.
    partial: Option<Rc<GlobalSubst>>,
    /// Unsolved holes as `0`, and as `1`: the two markers of `committed_*`.
    zero: Option<Rc<GlobalSubst>>,
    one: Option<Rc<GlobalSubst>>,
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
    /// A plain `match` on an elaborated scrutinee the goal does not mention
    /// (`Branches`): no equation, the motive the goal.
    Branches { scrut: Term, ty: Type, level: Level, motive: Type, arms: Vec<heather_syntax::Arm> },
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
    /// ([`HostMut::elab_generate`]), in a context of the length given.
    /// They were built in a world of `psi` globals, and the declarations
    /// published since are shifted past.
    /// `checked`: a body is compared with the type it is elaborated at
    /// (a registered member's, which is written by name).
    Member { fills: Vec<(Held, usize)>, psi: usize, checked: bool },
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
            substs: RefCell::default(),
            trail: Vec::new(),
            globals: Vec::new(),
            splits: Vec::new(),
            span,
            generator,
            readings: std::collections::HashMap::new(),
            shared: std::collections::HashMap::new(),
            said: Vec::new(),
            surfaces: std::collections::HashMap::new(),
            surface_error: None,
        }
    }

    /// The handles an invocation's arguments quoted, in order, at the root.
    fn issue_quoted(&mut self, quoted: Vec<Quoted>) {
        for q in quoted {
            match q {
                Quoted::Held(held) => {
                    self.issue(0, held);
                }
                Quoted::Surface(e) => {
                    // A placeholder `held` never reads: it answers for the
                    // surface term first.
                    let h = self.issue(0, Held::Type(Type::Nat, Level::Zero));
                    self.surfaces.insert(h, e);
                }
            }
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
        if self.surfaces.contains_key(&h) {
            return Err(Fault::Ill(format!(
                "handle {h} is a term the tactic was handed whose type is decided by where it stands (an \
                 unannotated `λ`): it can be an application's argument or the tactic's result, and nothing can \
                 ask about it"
            )));
        }
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

    /// The deepest scope enclosing both `a` and `b`.
    fn common_scope(&self, a: usize, b: usize) -> usize {
        let mut c = a;
        while !self.encloses(c, b) {
            c = self.scopes[c].parent.expect("the root scope encloses every scope");
        }
        c
    }

    /// A handle's term and type moved out from under the binders of its
    /// scope `s` that `at` is not under: scoped in the deepest scope
    /// enclosing both, which `lift` then weakens to `at`. Refused when it
    /// mentions one of those binders' locals. A handle is usable wherever
    /// what it mentions is in scope, not only under the binders it was
    /// found beneath: an arm's body read under its payload's binder is a
    /// function of the outer locals once it does not mention the payload
    /// (`rt_io_bridge`'s loop body under a `Bool` arm).
    fn strengthened(&self, s: usize, at: usize, term: &Term, ty: &Type) -> Result<(usize, Term, Type), Fault> {
        let c = self.common_scope(s, at);
        let d = (self.len(s) - self.len(c)) as u32;
        let gamma = self.cx(c)?.gamma;
        match (crate::unification::strengthen_tm(&gamma, term, d), crate::unification::strengthen_ty(&gamma, ty, d)) {
            (Some(t), Some(y)) => Ok((c, t, y)),
            _ => Err(Fault::Protocol("a handle is used outside the binder it lives under, and it mentions that binder's local".into())),
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
        // A shift by nothing is the solution itself, shared: this is asked
        // for at every application a generator's expression has, and a copy
        // of every solution each time was most of a long generator's run.
        let entries = self.holes.iter().enumerate().map(|(j, h)| GlobalEntry::Tm(match &h.sol {
            Some(t) if solved_shift == 0 => Rc::clone(t),
            Some(t) => Rc::new(t.shift_global(solved_shift)),
            None => Rc::new(unsolved(j)),
        })).collect();
        GlobalSubst { entries }
    }

    /// A new hole.
    fn add_hole(&mut self, hole: Hole) {
        self.holes.push(hole);
        *self.substs.get_mut() = HoleSubsts::default();
    }

    /// Hole `j`'s solution, found or forgotten.
    fn set_solution(&mut self, j: usize, sol: Option<Rc<Term>>) {
        self.holes[j].sol = sol;
        *self.substs.get_mut() = HoleSubsts::default();
    }

    /// The committed tests' two substitutions: unsolved holes as `0`, and
    /// as `1`.
    fn markers(&self) -> (Rc<GlobalSubst>, Rc<GlobalSubst>) {
        let mut memo = self.substs.borrow_mut();
        let zero = Rc::clone(memo.zero.get_or_insert_with(|| Rc::new(self.sigma(0, |_| Term::Zero))));
        let one = Rc::clone(memo.one.get_or_insert_with(|| Rc::new(self.sigma(0, |_| Term::Succ(Rc::new(Term::Zero))))));
        (zero, one)
    }

    /// `partial_*`'s substitution: solutions shifted past the world, the
    /// unsolved holes kept as their occurrences.
    fn partial_sigma(&self) -> Rc<GlobalSubst> {
        let m = self.world() as u32;
        let mut memo = self.substs.borrow_mut();
        Rc::clone(memo.partial.get_or_insert_with(|| Rc::new(self.sigma(m, |j| self.occurrence(j)))))
    }

    /// `t` in the committed world, if every hole it mentions is solved: the
    /// two-marker test of `unification::zonked`.
    fn committed_ty(&self, t: &Type) -> Option<Type> {
        if self.holes.is_empty() {
            return Some(t.clone());
        }
        let (zero, one) = self.markers();
        let a = t.apply_global(&zero);
        (a == t.apply_global(&one)).then_some(a)
    }

    fn committed_tm(&self, t: &Term) -> Option<Term> {
        if self.holes.is_empty() {
            return Some(t.clone());
        }
        let (zero, one) = self.markers();
        let a = t.apply_global(&zero);
        (a == t.apply_global(&one)).then_some(a)
    }

    /// Hole `j`'s occurrence at its home, in the current world.
    fn occurrence(&self, j: usize) -> Term {
        Term::GlobalTm {
            var: GlobalVar::index((self.world() - 1 - j) as u32),
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
        t.shift_global_above(m, m).apply_global(&self.partial_sigma())
    }

    fn partial_tm(&self, t: &Term) -> Term {
        let m = self.world() as u32;
        if m == 0 {
            return t.clone();
        }
        t.shift_global_above(m, m).apply_global(&self.partial_sigma())
    }

    /// Scope `s`'s context in the committed world, if no unsolved hole is
    /// in it.
    fn cx(&self, s: usize) -> Result<Cx, Fault> {
        let scope = &self.scopes[s];
        if scope.world == 0 {
            return Ok(scope.cx.clone());
        }
        let gamma = scope.cx.gamma.shift_global((self.world() - scope.world) as u32);
        let (zero, one) = self.markers();
        let a = gamma.apply_global(&zero);
        if a != gamma.apply_global(&one) {
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
            self.set_solution(j, None);
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
    /// The name of the type the value is registered under.
    registered: Option<String>,
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
/// What a tactic's argument quoted: an elaborated term or type, or surface
/// syntax whose type only its place in the tactic's result decides.
#[derive(Clone)]
pub(crate) enum Quoted {
    Held(Held),
    /// A term that infers no type of its own (an unannotated `λ`), checked
    /// where the result places it ([`Host::check_surface`]).
    Surface(Expr),
}

pub(crate) struct Quoting {
    /// `tactic::Expr` and its level.
    expr: Type,
    level: Level,
    /// `tactic::host_quote`'s head and type.
    quote: (Term, Rc<Type>),
    /// The goal's context, where every quoted term must live.
    root: LocalCtx,
    /// The quoted terms and types, in handle order after the goal.
    terms: RefCell<Vec<Quoted>>,
    /// The expression being checked without quoting, by the probe that
    /// decides whether it needs quoting at all.
    plain: Cell<Option<Span>>,
    /// A generator's run issues no goal handle, so its quoted terms are
    /// handles 0 onwards.
    no_goal: bool,
}

/// The tactic host's part of the elaborator: what answers a running tactic's requests.
pub(crate) struct Host<'e>(pub(crate) &'e Elaborator);

impl std::ops::Deref for Host<'_> {
    type Target = Elaborator;
    fn deref(&self) -> &Elaborator {
        self.0
    }
}

impl Host<'_> {
    /// `tactic::name`'s absolute index: by the name where the `by` is, or,
    /// where the module only imports `tactic` through another (a tactic
    /// library such as `set_tactic`), by its key in the import closure, as
    /// `Lookup` reaches a qualified name. A `by` needs the protocol loaded,
    /// not its short names (`pure`, `goal`, `open`, …) in scope, where they
    /// would rival the client's own members.
    pub(crate) fn protocol_abs(&self, name: &str) -> Option<usize> {
        let key = format!("tactic::{name}");
        self.global_abs(&key).or_else(|| {
            (self.names.reaches("tactic") && self.names.declares("tactic", name))
                .then(|| self.names.global(&key).map(|info| info.abs as usize))
                .flatten()
        })
    }

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
        self.speak(&world, closed, |speaker| self.run_tactic(cx, speaker, &shown, goal, lvl, quoted, span))
    }

    /// `tactic::name`'s head and type in `world`.
    fn protocol_signature(&self, world: &GlobalCtx, name: &str, keyword: &str, span: Span) -> R<(Term, Type)> {
        let key = format!("tactic::{name}");
        let Some(abs) = self.protocol_abs(name) else {
            return err(format!("`{keyword}` runs a value of the `tactic` protocol; add `import tactic;` (or import a tactic library that does)"), span);
        };
        let GlobalBinding::Tm { ty, .. } = &world.bindings[abs] else {
            return err(format!("`{key}` is not a term-level global"), span);
        };
        let var = world.reference(abs).expect("a binding of the world");
        let head = Term::GlobalTm { var, subst: LocalSubst::id(&LocalCtx::nil()) };
        Ok((head, ty.shift_global(var.rescope())))
    }

    /// Elaborate `e`, a `by`'s tactic or a `generate`'s generator, at the
    /// type `tactic::entry` takes, with quoting on: a closed term and the
    /// handles its arguments quoted. A generator issues no goal handle, so
    /// its quoted handles start at 0.
    fn protocol_value(&self, cx: &Cx, world: &GlobalCtx, e: &Expr, entry: &str, keyword: &str, span: Span) -> R<(Term, Vec<Quoted>)> {
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
            return Ok(Some(self.quoted(&q, cx, Quoted::Held(Held::Type(ty, level)), e.span)?));
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
            return Ok(Some(self.quoted(&q, cx, Quoted::Held(Held::Term(term.shift_local(root), ty.shift_local(root), level)), e.span)?));
        }
        q.plain.set(Some(e.span));
        let inferred = self.probe(|| {
            let inferred = self.elab_infer(cx, e);
            q.plain.set(None);
            match inferred {
                Err(_) => None,
                Ok((_, ty, level)) => Some(level.equiv(&q.level) && self.conv_types(cx, &ty, &q.expr, &level)),
            }
        });
        match inferred {
            Some(true) => return Ok(None),
            Some(false) => {}
            None => {
                // No type of its own (an unannotated `λ`): unless it is an
                // `Expr` after all, it is held as written and checked where
                // the tactic's result places it, at the type that place
                // expects (`Elaborator::check_surface`). Only directly under
                // the goal's context, where nothing the tactic expression
                // binds can be in scope.
                if q.no_goal || cx.gamma.len() != q.root.len() {
                    return Ok(None);
                }
                let before = q.terms.borrow().len();
                q.plain.set(Some(e.span));
                let is_expr = self.probe(|| {
                    let checked = self.elab_check(cx, e, expected, lvl).is_ok();
                    q.plain.set(None);
                    checked
                });
                q.terms.borrow_mut().truncate(before);
                if is_expr {
                    return Ok(None);
                }
                return Ok(Some(self.quoted(&q, cx, Quoted::Surface(e.clone()), e.span)?));
            }
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
        Ok(Some(self.quoted(&q, cx, Quoted::Held(Held::Term(term, ty, level)), e.span)?))
    }

    /// Record a quoted term of the goal's context and return the closed
    /// `host_quote(n)` that stands for it, weakened to `cx`.
    fn quoted(&self, q: &Quoting, cx: &Cx, held: Quoted, span: Span) -> R<Term> {
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
        quoted: Vec<Quoted>,
        span: Span,
    ) -> R<Term> {
        let fail = |msg: String| err(format!("`by {shown}`: {msg}"), span);
        let mut run = Run::new(cx, span, false);
        run.issue(0, Held::Type(goal.clone(), lvl.clone()));
        run.issue_quoted(quoted);
        self.issue_lets(cx, &mut run);
        match self.drive(&mut run, speaker) {
            Ok(Ended::Result(e)) => {
                let proof = match self.finish(&mut run, &e, cx, goal, lvl) {
                    Ok(proof) => proof,
                    Err(msg) => {
                        return match run.surface_error.take() {
                            Some(failure) => Err(failure),
                            None => fail(msg),
                        };
                    }
                };
                // What the run said is reported only now that it succeeded,
                // as one warning: the lints are kept one per span.
                if !run.said.is_empty() {
                    self.emit_lint(crate::Lint::TacticReport, format!("`by {shown}`: {}", run.said.join("\n")), span);
                }
                Ok(proof)
            }
            Ok(Ended::Published(_)) => fail("only `generate` publishes declarations".into()),
            Err(msg) => match run.surface_error.take() {
                Some(failure) => Err(failure),
                None => fail(msg),
            },
        }
    }

    /// The host loop: drive `speaker` until it returns a result or, in a
    /// generator's run, publishes, answering its requests in the run's
    /// scopes. The error is the reason the run stopped.
    fn drive(&self, run: &mut Run, speaker: &mut dyn Speaker) -> Result<Ended, String> {
        let span = run.span;
        let what = if run.generator { "generator" } else { "tactic" };
        let budget = if run.generator { GENERATOR_REQUEST_BUDGET } else { REQUEST_BUDGET };
        let mut step = speaker.start();
        for answered in 0..budget {
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
                Request::Cases(e, goal) => Answer::Split(refusable(self.cases_request(run, &e, goal, false))?),
                Request::Branches(e, goal) => Answer::Split(refusable(self.cases_request(run, &e, goal, true))?),
                Request::Constructor(goal) => Answer::Split(refusable(self.constructor_request(run, goal))?),
                Request::Close(split, proofs) => Answer::Handle(refusable(self.close_request(run, split, &proofs))?),
                Request::Assume(ty, name, under) => Answer::Local(refusable(self.assume_request(run, &ty, name, under))?),
                Request::Ctors(h) => Answer::Ctors(refusable(self.ctors_request(run, h))?),
                Request::AsType(e) => Answer::Handle(refusable(self.as_type_request(run, &e))?),
                Request::Holes(e, n) => Answer::Holes(refusable(self.holes_request(run, &e, n))?),
                Request::Body(g) => Answer::Handle(refusable(self.body_request(run, g))?),
                Request::Modes(g) => Answer::Modes(refusable(self.modes_request(run, g))?),
                Request::Arms(h) => Answer::Arms(refusable(self.arms_request(run, h))?),
                Request::Synth(h) => Answer::Handle(refusable(self.synth_request(run, h, span))?),
                Request::Spine(h) => Answer::Spine(refusable(self.spine_request(run, h))?),
                Request::Fields(e) => Answer::Fields(refusable(self.fields_request(run, &e))?),
                Request::Inj(e, k) => Answer::Handle(refusable(self.inj_request(run, &e, k, span))?),
                Request::Absurd(e, goal) => Answer::Handle(refusable(self.absurd_request(run, &e, goal, span))?),
                Request::Unfold(h) => Answer::Handle(refusable(self.unfold_request(run, h))?),
                Request::Repr(ty) => Answer::Handle(refusable(self.repr_request(run, ty))?),
                Request::Spell(e) => Answer::Handle(refusable(self.spell_request(run, &e))?),
                Request::Abstract(h, x) => Answer::Handle(refusable(self.abstract_request(run, h, &x))?),
                Request::Revert(h, x) => Answer::Handle(refusable(self.revert_request(run, h, &x))?),
                Request::Simp(laws, goal) => Answer::Handle(refusable(self.simp_request(run, &laws, goal, span))?),
                Request::SimpCheck(laws) => Answer::Handle(refusable(self.simp_check_request(run, &laws, span))?),
                Request::Numeral(e) => Answer::Handle(refusable(self.numeral_request(run, &e))?),
                Request::Sat(cs, vars) => Answer::Sat(refusable(self.sat_request(run, &cs, vars))?),
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
        Err(format!("the {what} made more than {budget} requests without finishing"))
    }

    /// The tactic's result as a proof of the goal: elaborated, compared with
    /// the goal (which may solve holes), and in the committed world.
    fn finish(&self, run: &mut Run, e: &RExpr, cx: &Cx, goal: &Type, lvl: &Level) -> Result<Term, String> {
        if let RExpr::Hd(h) = e
            && run.surfaces.contains_key(h)
        {
            let shifted = goal.shift_global(run.world() as u32);
            let term = self.check_surface(run, *h, &shifted, lvl, 0).map_err(Fault::msg)?;
            return run.committed_tm(&term).ok_or_else(|| "the tactic's proof mentions a hole nothing solved".to_string());
        }
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

    /// Did comparing two committed types run out of fuel (rather than find
    /// them different)? Asked only on the way to reporting a mismatch.
    fn ty_conv_out_of_fuel(&self, run: &mut Run, at: usize, a: &Type, b: &Type, lvl: &Level) -> bool {
        let (pa, pb) = (run.partial_ty(a), run.partial_ty(b));
        let (Some(x), Some(y)) = (run.committed_ty(&pa), run.committed_ty(&pb)) else { return false };
        let Ok(cx) = run.cx(at) else { return false };
        matches!(
            self.goal_oracle().convert_type(&cx.gamma, Layer::Prog, &x, &y, lvl),
            Err(heather_kernel::conv::ConvError::OutOfFuel)
        )
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
            AppUnify(self).unify_under(&hcx, pat, subj, m as u32, d, &mut trial, &[], run.span);
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
                run.set_solution(j, Some(t));
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
        let names = (0..run.world()).map(|j| (GlobalVar::index(first + j as u32), format!("?{}", j + 1))).collect();
        let sigma = run.sigma(0, |j| Term::GlobalTm {
            var: GlobalVar::index(first + j as u32),
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
    /// `Modes(g)`: the access mode each parameter of `g`'s table was
    /// declared with (docs/language/sequencing-surface-design.md §24), type
    /// parameters and implicit ones included, so the list lines up with the
    /// `λ`s `Body` opens. Refused for a global with no declared table.
    fn modes_request(&self, run: &mut Run, g: u64) -> Result<Vec<heather_syntax::ParamMode>, Fault> {
        let key = run.globals.get(g as usize).cloned().ok_or_else(|| Fault::Ill(format!("{g} is not a global this run issued")))?;
        let GlobalKey::At(abs) = key else {
            return Err(Fault::Ill("a type or a kernel former declares no parameters".into()));
        };
        let name = self.global_name_at(abs as usize).unwrap_or_else(|| "this global".into());
        let Some(params) = self.names.params_at(abs as u32) else {
            return Err(Fault::Ill(format!("`{name}` has no declared parameter table")));
        };
        Ok(params.iter().map(|p| p.mode).collect())
    }

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

    /// `Unfold(h)`: the term `h` stands for, its head definition replaced
    /// by its body and the β-redexes at the head contracted, so `f(a, b)`
    /// reads as `f`'s body at `a` and `b` (implicit arguments included) and
    /// nothing else is reduced. Refused where `Body` is, for a head that is
    /// not a global, and in a scope under unsolved holes.
    fn unfold_request(&self, run: &mut Run, h: u64) -> Result<u64, Fault> {
        let (at, held) = run.held(h)?;
        let Held::Term(t, ty, level) = held else { return Err(Fault::Ill(format!("handle {h} stands for a type, not a call"))) };
        let t = run.committed_tm(&t).ok_or_else(|| Fault::Ill("it mentions a hole nothing has solved".into()))?;
        let ty = run.committed_ty(&ty).ok_or_else(|| Fault::Ill("its type mentions a hole nothing has solved".into()))?;
        if run.scopes[at].world != 0 {
            return Err(Fault::Ill("it is under holes nothing has solved".into()));
        }
        let (head, args) = crate::spelling::app_spine(&t);
        let Term::GlobalTm { var, .. } = head else {
            // A head that computes without a definition, a β-redex or a
            // `match` on a constructor (a word chosen by a test, at the
            // test's outcome): its β and ι steps, no global unfolded, so the
            // arm it selects is read as written.
            let gamma = run.cx(at)?.gamma;
            let w = self.goal_oracle().whnf_term_opaque(&gamma, &t).map_err(|_| Fault::Ill("ran out of fuel reducing it".into()))?;
            if w != t {
                return Ok(run.issue(at, Held::Term(w, ty, level)));
            }
            return Err(Fault::Ill("its head is not a global, so there is no definition to unfold".into()));
        };
        let abs = self.global_abs_of(*var).ok_or_else(|| Fault::Ill("its head is not a global this run can read".into()))?;
        let name = self.global_name_at(abs).unwrap_or_else(|| "this global".into());
        let world = self.goal_psi();
        let len = world.bindings.len();
        let Some(GlobalBinding::Tm { ctx, ty: gty, body, .. }) = world.bindings.get(abs) else {
            return Err(Fault::Ill(format!("`{name}` is not a term")));
        };
        let Some(body) = body else {
            return Err(Fault::Ill(format!("`{name}` has no body to unfold: a theorem's proof is not kept, and an axiom has none")));
        };
        if !ctx.entries.is_empty() || matches!(**gty, Type::UPi { .. }) {
            return Err(Fault::Ill(format!("`{name}` is universe-polymorphic or context-dependent, and its body is not read yet")));
        }
        let locals = run.cx(at)?.gamma.len() as u32;
        let mut out = body.shift_global((len - abs) as u32).shift_local(locals);
        for a in args {
            out = Term::AppAt { fun: Rc::new(out), arg: Rc::clone(a) };
        }
        let out = crate::spelling::beta_head(&out).unwrap_or(out);
        Ok(run.issue(at, Held::Term(out, ty, level)))
    }

    /// `Spell(e)`: the term `e` stands for, spelled one definition further
    /// on. Its head definition is unfolded and the head reduced on, by the
    /// elaborator's reduct walk (`Unfold::Spelling`), until the first reduct
    /// headed by a global's call or a local, or the walk's end (a value, or a
    /// stuck form, which the caller tells apart by `View`). Projections of
    /// the reduct's pairs are read off, as `Whnf` reads them. Refused when
    /// nothing at the head reduces (a local's call, a call of an opaque or
    /// withheld definition: an `interface fn`'s body is not this world's to
    /// read) and when the walk's budget runs out first. What a reader that
    /// follows a term through its definitions, one call at a time, reads
    /// (docs/tactics/grind-design.md §15).
    fn spell_request(&self, run: &mut Run, e: &RExpr) -> Result<u64, Fault> {
        let at = run.scope_of(e)?;
        let mark = run.trail.len();
        let r = self.reify(run, e, at).inspect_err(|_| run.restore(mark))?;
        let (Some(t), Some(ty)) = (run.committed_tm(&r.term), run.committed_ty(&r.ty)) else {
            run.restore(mark);
            return Err(Fault::Ill("it mentions a hole nothing has solved".into()));
        };
        let gamma = run.cx(at)?.gamma;
        // Through the interface boundary as conversion sees it: another
        // module's `interface fn` stays folded at open arguments
        // (docs/language/interface-definitions-design.md §3), so no spelling it
        // returns is one the gate would refuse to convert.
        let world = match InterfaceDefs(self).withheld_policy() {
            Some(w) => self.goal_psi().withholding(Some(w)),
            None => self.goal_psi(),
        };
        let oracle = crate::oracle::SemanticOracle::in_world(world, self.policy.fuel);
        let mut last = None;
        for reduct in oracle.unfold(&gamma, &t, Unfold::Spelling) {
            let (head, _) = crate::spelling::app_spine(&reduct);
            if matches!(head, Term::GlobalTm { .. } | Term::Var(_)) {
                let out = (*crate::spelling::contract_projections(&Rc::new(reduct))).clone();
                return Ok(run.issue(at, Held::Term(out, ty, r.level)));
            }
            last = Some(reduct);
        }
        let Some(end) = last else {
            return Err(Fault::Ill("nothing at its head reduces: a local, or a definition this world does not unfold".into()));
        };
        // The walk stopped: at a head normal form, or at the budget.
        match oracle.bounded(1).unfold(&gamma, &end, Unfold::OneStep).next() {
            None => {
                let out = (*crate::spelling::contract_projections(&Rc::new(end))).clone();
                Ok(run.issue(at, Held::Term(out, ty, r.level)))
            }
            Some(_) => Err(Fault::Ill("its head reduces past the walk's budget before a call is at the head again".into())),
        }
    }

    /// `Numeral(e)`: the numeral a closed term of type `Nat` computes to,
    /// as a handle `View` shows as `HLit`. The term is run in the kernel's
    /// value domain, where a tactic's own values are computed
    /// ([`Reader::nat`]), so a library function over numerals costs its
    /// steps there. `Whnf` walks the term instead and declines where a
    /// function that recurses by steps is under the head (`Nat::round_up`
    /// is past its budget at two digits), which is why a generator that
    /// asks the library for a number asks here. Refused for a term that is
    /// not a `Nat`, that mentions a local, or whose value is not a numeral
    /// within the reader's budget.
    fn numeral_request(&self, run: &mut Run, e: &RExpr) -> Result<u64, Fault> {
        let at = run.scope_of(e)?;
        let mark = run.trail.len();
        let r = self.reify(run, e, at).inspect_err(|_| run.restore(mark))?;
        let (Some(t), Some(ty)) = (run.committed_tm(&r.term), run.committed_ty(&r.ty)) else {
            run.restore(mark);
            return Err(Fault::Ill("it mentions a hole nothing has solved".into()));
        };
        let gamma = run.cx(at)?.gamma;
        if !matches!(self.goal_oracle().whnf_type(&gamma, &ty), Ok(Type::Nat)) {
            return Err(Fault::Ill(format!("it is a `{}`, and a numeral is a `Nat`", self.shown_ty(run, at, &ty))));
        }
        let t = Rc::new(t);
        if heather_kernel::subst::local_bound(&t) != 0 {
            return Err(Fault::Ill("it mentions a local, and only a closed term computes to a numeral".into()));
        }
        let world = self.goal_psi();
        let arena = ValueArena::new();
        let reader = Reader::new(&world, &arena);
        let n = reader.nat(reader.root((*t).clone())).map_err(|why| Fault::Ill(format!("it does not compute to a numeral: {why}")))?;
        let n = usize::try_from(n).map_err(|_| Fault::Ill("its numeral is past this machine's word".into()))?;
        Ok(run.issue(at, Held::Term(crate::inductive::nat_lit(n), Type::Nat, Level::Zero)))
    }

    /// `Abstract(h, x)`: `λ y => h[y/x]`, for `x` a local of the goal's
    /// context, a function of `x`'s type. A type is abstracted as its code,
    /// so abstracting a goal over `n` and then `m` is the motive
    /// `λ a b => goal[a/m, b/n]` a case lemma takes (`wlog`,
    /// issues/wlog-symmetric-cases.md). Only `h` is abstracted: a later
    /// local whose type mentions `x` keeps meaning the original one, which
    /// is still in scope, so the abstraction is well typed whatever `h`
    /// mentions; nothing here is trusted, as the kernel checks the proof
    /// that uses it.
    fn abstract_request(&self, run: &mut Run, h: u64, x: &RExpr) -> Result<u64, Fault> {
        let unsolved = || Fault::Ill("it mentions a hole nothing has solved".into());
        let (at, held) = run.held(h)?;
        let (term, ty, level) = match held {
            Held::Type(t, l) => {
                let t = run.committed_ty(&t).ok_or_else(unsolved)?;
                let Some(c) = crate::code::code_of(&t) else {
                    return Err(Fault::Ill(format!("the type `{}` has no code to abstract", self.shown_ty(run, at, &t))));
                };
                (c, Type::Ty(l.clone()), Level::succ(l))
            }
            Held::Term(t, ty, l) => (run.committed_tm(&t).ok_or_else(unsolved)?, run.committed_ty(&ty).ok_or_else(unsolved)?, l),
        };
        // A term that is not a local (a test `b < 0x80` in an `if`): every
        // occurrence of it, as written, a mention of the parameter, which
        // `bv_decide` reads a word chosen by a test through. The body is
        // abstracted inside a type wrapper, the one form the abstraction
        // walks; the wrapper is not a type the result is ever read as.
        if !matches!(x, RExpr::Local(_)) && self.root_local_position(run, x).is_err() {
            // `x` may live under more binders than `h` (an atom found inside
            // the goal, `h` a hypothesis's statement): both are read in the
            // deeper scope.
            let to = run.join(run.scope_of(x)?, at)?;
            let term = run.lift(at, to, |k| term.shift_local(k))?;
            let ty = run.lift(at, to, |k| ty.shift_local(k))?;
            let at = to;
            let mark = run.trail.len();
            let r = self.reify(run, x, at).inspect_err(|_| run.restore(mark))?;
            let pat = run.committed_tm(&run.partial_tm(&r.term)).ok_or_else(unsolved)?;
            let dom = Rc::new(run.committed_ty(&run.partial_ty(&r.ty)).ok_or_else(unsolved)?);
            // No occurrence is the constant function, as for a local `h`
            // does not mention.
            let wrapped = Type::El { level: level.clone(), tm: Rc::new(term.clone()) };
            let body = match wrapped.abstract_local(&pat) {
                Some(Type::El { tm, .. }) => (*tm).clone(),
                Some(_) => unreachable!("abstraction keeps the wrapper"),
                None => term.shift_local(1),
            };
            let cod = ty.abstract_local(&pat).unwrap_or_else(|| ty.shift_local(1));
            let lam = Term::Lam { dom_level: r.level.clone(), cod_level: level.clone(), dom: Rc::clone(&dom), body: Rc::new(body) };
            let pi = Type::Pi { dom_level: r.level.clone(), cod_level: level.clone(), dom, cod: Rc::new(cod) };
            return Ok(run.issue(at, Held::Term(lam, pi, Level::max(r.level, level))));
        }
        let p = self.root_local_position(run, x)?;
        let gamma = run.cx(at)?.gamma;
        let n = gamma.len();
        let entry = gamma.entries.get(p).expect("a local of the goal's context");
        let dom_level = entry.level.clone();
        let dom = Rc::new(entry.ty.shift_local((n - p) as u32));
        let sigma = crate::generalize::rename(&gamma, &[p], 1);
        let body = term.apply_local(&sigma);
        let cod = ty.apply_local(&sigma);
        let lam = Term::Lam { dom_level: dom_level.clone(), cod_level: level.clone(), dom: Rc::clone(&dom), body: Rc::new(body) };
        let pi = Type::Pi { dom_level: dom_level.clone(), cod_level: level.clone(), dom, cod: Rc::new(cod) };
        Ok(run.issue(at, Held::Term(lam, pi, Level::max(dom_level, level))))
    }

    /// `Revert(h, x)`: the type `(y: X) → h[y/x]` for `x` a local of the
    /// goal's context of type `X`; what `wlog` makes of a hypothesis about
    /// its points before abstracting them. As with `Abstract`, a later local
    /// whose type mentions `x` keeps meaning the original one.
    ///
    /// `x` may also be a global `g: X`: the type `(y: X) → h[y/g]`, every
    /// mention of the global a parameter (the constant function where there
    /// is none). A generator proves a statement by conversion there, where
    /// the name has no body to unfold, and applies the proof to `g`.
    fn revert_request(&self, run: &mut Run, h: u64, x: &RExpr) -> Result<u64, Fault> {
        let (at, held) = run.held(h)?;
        let (ty, level) = match held {
            Held::Type(t, l) => (run.committed_ty(&t).ok_or_else(|| Fault::Ill("it mentions a hole nothing has solved".into()))?, l),
            Held::Term(..) => return Err(Fault::Ill(format!("handle {h} stands for a term, not a type"))),
        };
        // A global: the type with each mention of it a parameter of the
        // global's type. What is proved at the parameter is proved of a
        // name with no body to unfold, and is then read at the global.
        if let RExpr::Global(_) = x {
            let unsolved = || Fault::Ill("the global's term or type mentions a hole nothing has solved".into());
            let mark = run.trail.len();
            let r = match self.reify(run, x, at) {
                Ok(r) => r,
                Err(f) => {
                    run.restore(mark);
                    return Err(f);
                }
            };
            let pat = run.committed_tm(&run.partial_tm(&r.term)).ok_or_else(unsolved)?;
            let dom = Rc::new(run.committed_ty(&run.partial_ty(&r.ty)).ok_or_else(unsolved)?);
            let cod = ty.abstract_local(&pat).unwrap_or_else(|| ty.shift_local(1));
            let pi = Type::Pi { dom_level: r.level.clone(), cod_level: level.clone(), dom, cod: Rc::new(cod) };
            return Ok(run.issue(at, Held::Type(pi, Level::max(r.level, level))));
        }
        let p = self.root_local_position(run, x)?;
        let gamma = run.cx(at)?.gamma;
        let n = gamma.len();
        let entry = gamma.entries.get(p).expect("a local of the goal's context");
        let dom_level = entry.level.clone();
        let dom = Rc::new(entry.ty.shift_local((n - p) as u32));
        let cod = ty.apply_local(&crate::generalize::rename(&gamma, &[p], 1));
        let pi = Type::Pi { dom_level: dom_level.clone(), cod_level: level.clone(), dom, cod: Rc::new(cod) };
        Ok(run.issue(at, Held::Type(pi, Level::max(dom_level, level))))
    }

    /// The position in the goal's context of the local `x` names: a
    /// `Local` of the goal, or a handle to one (a quoted `m`).
    fn root_local_position(&self, run: &Run, x: &RExpr) -> Result<usize, Fault> {
        let not_local = || Fault::Ill("only a local of the goal's context (not a `let`) can be abstracted".into());
        match x {
            RExpr::Local(id) if run.let_local(*id).is_none() => match run.local(*id)? {
                (0, i) => Ok(i),
                _ => Err(not_local()),
            },
            RExpr::Hd(h) => match run.held(*h)? {
                (s, Held::Term(Term::Var(LocalVar(k)), ..)) => {
                    let i = run.len(s) - 1 - k as usize;
                    if i < run.len(0) { Ok(i) } else { Err(not_local()) }
                }
                _ => Err(not_local()),
            },
            _ => Err(not_local()),
        }
    }

    /// `Repr(ty)`: the representation registered for the type `ty` stands
    /// for (`datarepr`, docs/native/datarepr-design.md §1.4), as a handle to the
    /// repr's assembled value. A type is keyed as the declaration keys it: a
    /// declaration with no parameters by its tag, one with value parameters
    /// by its tag and its arguments, which must be numerals (`SInt(64)`);
    /// type arguments are not read yet.
    fn repr_request(&self, run: &mut Run, h: u64) -> Result<u64, Fault> {
        let (at, held) = run.held(h)?;
        let Held::Type(ty, level) = held else { return Err(Fault::Ill(format!("handle {h} stands for a term, not a type"))) };
        let ty = run.committed_ty(&ty).ok_or_else(|| Fault::Ill("it mentions a hole nothing has solved".into()))?;
        let cx = run.cx(at)?;
        let ty = self.unspell_here(&ty).unwrap_or(ty);
        let ind = self.display_tag_of(&ty).ok_or_else(|| Fault::Ill("it is not a declared inductive, which is what a repr represents".into()))?;
        let argkey = if ind.params.is_empty() && ind.valparams.is_empty() {
            String::new()
        } else if ind.params.is_empty() && ind.index.is_none() {
            let args = self.value_args(&cx, &ty, &level, &ind)
                .ok_or_else(|| Fault::Ill(format!("`{}`'s arguments could not be read", ind.name)))?;
            let mut spelled = Vec::with_capacity(args.len());
            for a in &args {
                let n = crate::inductive::nat_value(a)
                    .ok_or_else(|| Fault::Ill(format!("`{}` at an argument that is not a numeral has no repr: a repr is per instantiation", ind.name)))?;
                spelled.push(n.to_string());
            }
            spelled.join(",")
        } else {
            return Err(Fault::Ill(format!("`{}` takes type arguments, and a repr's type arguments are not read yet", ind.name)));
        };
        let global = self.representations.for_spec(&(Some(ind.tag), argkey))
            .map(|info| info.global.clone())
            .ok_or_else(|| Fault::Ill(format!("`{}` has no repr registered here", self.shown_ty(run, at, &ty))))?;
        let (term, gty, glevel) = self.raw_global(&global)
            .ok_or_else(|| Fault::Ill(format!("the repr `{global}` is not a global here")))?;
        let n = run.cx(at)?.gamma.len() as u32;
        Ok(run.issue(at, Held::Term(term.shift_local(n), gty.shift_local(n), glevel)))
    }

    /// The value arguments a value-parameterized declaration's instance is
    /// at (`SInt(64)`'s `64`), read as [`Self::view_instance`] reads them:
    /// by unifying with the declaration's template at unknown arguments.
    fn value_args(&self, cx: &Cx, ty: &Type, level: &Level, ind: &crate::Inductive) -> Option<Vec<Rc<Term>>> {
        let m = (ind.params.len() + ind.valparams.len()) as u32;
        let mut code = self.gen_ref(crate::gendefs::GenDef::TyCodeFn(ind.tag))?;
        for j in 0..m {
            let meta = Term::GlobalTm { var: GlobalVar::index(j), subst: LocalSubst::id(&cx.gamma) };
            code = Term::AppAt { fun: Rc::new(code), arg: Rc::new(meta) };
        }
        let template = Type::El { level: level.clone(), tm: Rc::new(code) };
        let inline = self.unspell_here(&template)?;
        let mut sols = vec![Sol::Unsolved; m as usize];
        AppUnify(self).unify_root(cx, &inline, ty, m, &mut sols, &[], Span { start: 0, end: 0 });
        let solved = crate::unification::zonked(&inline, m, &sols)?;
        if !self.conv_types(cx, &solved, ty, level) {
            return None;
        }
        sols.iter().skip(ind.params.len()).map(|s| s.solved().cloned()).collect()
    }

    /// `Arms(h)`: the `match` `h` stands for, scrutinee and arms. A tier-0
    /// match on a two-constructor inductive (`Bool`) is one kernel `Case`,
    /// its arms the cases under the payload's binder; each is handed out as
    /// a λ over the payload. A `match h:` is that `Case` applied to `refl`,
    /// and the application's argument is listed. Wider matches nest `Case`s
    /// and are refused until a reader needs them.
    ///
    /// A field read of a `match`'s record (`(match c { … }).value.after`,
    /// which `View` shows as the `match`, stuck on its scrutinee) is that
    /// `match`, its arms whole, with the fields read listed by number, the
    /// first read first (`path`): a statement `if`'s joined locals are read
    /// so (docs/native/io-programs-design.md §4.2).
    fn arms_request(&self, run: &mut Run, h: u64) -> Result<ArmsView, Fault> {
        let (at, held) = run.held(h)?;
        let Held::Term(t, ..) = held else { return Err(Fault::Ill(format!("handle {h} stands for a type, not a match"))) };
        let mut t = run.committed_tm(&t).ok_or_else(|| Fault::Ill("it mentions a hole nothing has solved".into()))?;
        // A β-redex is its contractum, as `View` shows it: a body whose
        // `on` clauses bind obligations is the match under their `λ`s,
        // applied (a `runtime fn` with `on ?dec := …`).
        while let Some(r) = crate::spelling::beta_head(&t) {
            t = r;
        }
        // The projections, the outermost first; a field `i` is `fst` after
        // `i + 1` `snd`s (`DisplayCx::field_read_record`).
        let mut projs = Vec::new();
        let mut head = &t;
        while let Some((first, pair)) = crate::spelling::proj_of(head) {
            projs.push(first);
            head = pair;
        }
        let mut path = Vec::new();
        let mut snds = 0u64;
        for first in projs.iter().rev() {
            if *first {
                let Some(i) = snds.checked_sub(1) else { return Err(Fault::Ill("a projection of a `match` that is not a field read".into())) };
                path.push(i);
                snds = 0;
            } else {
                snds += 1;
            }
        }
        if snds != 0 {
            return Err(Fault::Ill("a projection of a `match` that is not a field read".into()));
        }
        // The record read may itself be a β-redex (a `match` under `on`
        // clauses' `λ`s, its field read).
        let reduced;
        if let Some(mut r) = crate::spelling::beta_head(head) {
            while let Some(r2) = crate::spelling::beta_head(&r) {
                r = r2;
            }
            reduced = r;
            head = &reduced;
        }
        let mut spine = Vec::new();
        while let Term::AppAt { fun, arg } = head {
            spine.push(arg);
            head = fun;
        }
        spine.reverse();
        // A `match` on a `Nat` that recurses (a fuel recursion's top match,
        // docs/native/runtime-fn-setups-design.md §16.11) is the kernel's `Nat`
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
            return Ok(ArmsView { scrut: s, arms: vec![("Zero".into(), zero), ("Succ".into(), succ)], args, path });
        }
        let Term::Case { scrut, .. } = head else {
            return Err(Fault::Ill("it is not a `match`".into()));
        };
        let (sty, slevel) = self.kernel_type(run, at, scrut).ok_or_else(|| Fault::Ill("its scrutinee has no type".into()))?;
        // A type of two constructors, or a flat one of more (an enum): a
        // `match` on the latter is a tree of `Case`s, one per `+` of the
        // type's sum (docs/inductives/inductive-tier0-lowering.md §5.2), each
        // inner one on the binder its parent's side bound.
        let ind = self
            .display_tag_of(&sty)
            .filter(|ind| ind.ctors.len() == 2 || (ind.ctors.len() > 2 && ind.flat() && ind.index.is_none()))
            .ok_or_else(|| Fault::Ill("only a `match` on a type with two constructors, or on a flat type of more, is presented yet".into()))?;
        let s = run.issue_shared(at, scrut, sty, slevel);
        let layout = crate::sum_layout::layout(ind.ctors.len());
        let mut found: Vec<Option<Term>> = vec![None; ind.ctors.len()];
        case_tree_arms(&layout, 0, head, 0, &mut found)?;
        let mut arms = Vec::with_capacity(ind.ctors.len());
        for (ctor, lam) in ind.ctors.iter().zip(found) {
            let lam = lam.ok_or_else(|| Fault::Ill("a constructor's arm is missing from the `match`".into()))?;
            let (aty, alevel) = self.kernel_type(run, at, &lam)
                .ok_or_else(|| Fault::Ill("an arm does not type as a function of its payload".into()))?;
            arms.push((ctor.name.clone(), run.issue(at, Held::Term(lam, aty, alevel))));
        }
        let mut args = Vec::with_capacity(spine.len());
        for a in spine {
            let (aty, alevel) = self.kernel_type(run, at, a).ok_or_else(|| Fault::Ill("an argument has no type".into()))?;
            args.push(run.issue_shared(at, a, aty, alevel));
        }
        Ok(ArmsView { scrut: s, arms, args, path })
    }

    /// `Spine(h)`: the term `h` stands for as a head applied to arguments,
    /// read off the kernel's applications with nothing reduced but a head β-redex: every
    /// argument, implicit ones included, in order, each with whether the
    /// function's type at it is dependent (its codomain mentions it, as a
    /// type argument's does). A term that is no application is its own head
    /// with no arguments. A subterm the term shares is one handle wherever
    /// it occurs (as for `Arms`), but equal subterms built apart are not:
    /// identity beyond sharing is `Defeq`'s (docs/tactics/grind-design.md §3).
    fn spine_request(&self, run: &mut Run, h: u64) -> Result<SpineView, Fault> {
        let (at, held) = run.held(h)?;
        let Held::Term(t, ..) = held else { return Err(Fault::Ill(format!("handle {h} stands for a type, not a term"))) };
        let t = run.committed_tm(&t).ok_or_else(|| Fault::Ill("it mentions a hole nothing has solved".into()))?;
        // A β-redex at the head is read as its contractum, as `View` shows
        // it: an instantiated λ (`(λ s => f(w, s))(x)`, which a `cong_fn` or
        // a lemma's function argument leaves in a type) is the call `f(w, x)`
        // (docs/tactics/grind-design.md §14.3).
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
    /// its own (docs/tactics/grind-design.md §12).
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
    /// (docs/metaprogramming/host-elaboration-interface-design.md §25).
    fn inj_request(&self, run: &mut Run, e: &RExpr, k: u64, span: Span) -> Result<u64, Fault> {
        let at = run.scope_of(e)?;
        let mark = run.trail.len();
        let r = self.reify(run, e, at).inspect_err(|_| run.restore(mark))?;
        let (Some(t), Some(ty)) = (run.committed_tm(&r.term), run.committed_ty(&r.ty)) else {
            run.restore(mark);
            return Err(Fault::Ill("it mentions a hole nothing has solved".into()));
        };
        let cx = run.cx(at)?;
        let (p, pty, plevel) = Inductives(self)
            .inj_of_term(&cx, k as usize, t, &ty, span)
            .map_err(|e| Fault::Ill(elab_message(e)))?;
        Ok(run.issue(at, Held::Term(p, pty, plevel)))
    }

    /// `Absurd(e, goal)`: `absurd(e)` at the type `goal` holds, from `e`, a
    /// proof of an equation between values of two different constructors
    /// (as the sides compute). Refused where the surface `absurd` is: one
    /// constructor on both sides, or sides that are no constructors'
    /// (docs/metaprogramming/host-elaboration-interface-design.md §25).
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
        let p = Inductives(self)
            .absurd_of_term(&cx, t, &ty, &expected, &glevel, span)
            .map_err(|e| Fault::Ill(elab_message(e)))?;
        Ok(run.issue(at, Held::Term(p, expected, glevel)))
    }

    /// `Simp(laws, goal)`: a proof of the type `goal` holds, by normalising
    /// it with the laws until its two sides meet, as `simp_only` does
    /// (`rewrite::Simps::simp_terms`). The laws are terms the tactic chose
    /// (a set's lemmas resolved, hypotheses), so which laws apply to which
    /// goal is the tactic's policy and the walk is the host's
    /// (docs/tactics/simp-design.md §7). A refusal is `simp_only`'s report, route
    /// included.
    fn simp_request(&self, run: &mut Run, laws: &[RExpr], goal: u64, span: Span) -> Result<u64, Fault> {
        let gs = run.held(goal)?.0;
        let mut at = gs;
        for law in laws {
            at = run.join(run.scope_of(law)?, at)?;
        }
        let mark = run.trail.len();
        let mut reified = Vec::with_capacity(laws.len());
        for law in laws {
            reified.push(self.reify(run, law, at).inspect_err(|_| run.restore(mark))?);
        }
        // The goal is read after the laws: reifying them may make holes.
        let (gty, glevel) = match run.held(goal)? {
            (_, Held::Type(t, l)) => (t, l),
            (_, Held::Term(..)) => return Err(Fault::Ill(format!("handle {goal} stands for a term, not a type"))),
        };
        let unsolved = || Fault::Ill("it mentions a hole nothing has solved".into());
        let expected = run.lift(gs, at, |k| gty.shift_local(k))?;
        let expected = run.committed_ty(&expected).ok_or_else(unsolved)?;
        let cx = run.cx(at)?;
        let mut terms = Vec::with_capacity(reified.len());
        for (i, r) in reified.iter().enumerate() {
            let (Some(t), Some(ty)) = (run.committed_tm(&r.term), run.committed_ty(&r.ty)) else {
                run.restore(mark);
                return Err(unsolved());
            };
            let name = self.spell_term_clean(&cx, &t).unwrap_or_else(|| format!("law {}", i + 1));
            terms.push((name, t, ty));
        }
        let p = crate::rewrite::Simps(self)
            .simp_terms(&cx, terms, &expected, &glevel, span)
            .map_err(|e| Fault::Ill(elab_message(e)))?;
        Ok(run.issue(at, Held::Term(p, expected, glevel)))
    }

    /// `SimpCheck(laws)`: the laws pass the checks a set is held to
    /// (`rewrite::Simps::check_terms`, docs/tactics/simp-design.md §4): none loops
    /// on its own statement, and none is rewritten by another to a result
    /// that does not join. Answered with `trivial`, a proof of `True`, so a
    /// check is a theorem beside the set; refused with the law and the
    /// route.
    fn simp_check_request(&self, run: &mut Run, laws: &[RExpr], span: Span) -> Result<u64, Fault> {
        let mut at = 0;
        for law in laws {
            at = run.join(run.scope_of(law)?, at)?;
        }
        let mark = run.trail.len();
        let mut reified = Vec::with_capacity(laws.len());
        for law in laws {
            reified.push(self.reify(run, law, at).inspect_err(|_| run.restore(mark))?);
        }
        let cx = run.cx(at)?;
        let mut terms = Vec::with_capacity(reified.len());
        for (i, r) in reified.iter().enumerate() {
            let (Some(t), Some(ty)) = (run.committed_tm(&r.term), run.committed_ty(&r.ty)) else {
                run.restore(mark);
                return Err(Fault::Ill("a law mentions a hole nothing has solved".into()));
            };
            let name = self.spell_term_clean(&cx, &t).unwrap_or_else(|| format!("law {}", i + 1));
            terms.push((name, t, ty, r.level.clone()));
        }
        crate::rewrite::Simps(self).check_terms(&cx, terms, span).map_err(|e| Fault::Ill(elab_message(e)))?;
        let level = Level::Zero;
        Ok(run.issue(at, Held::Term(Term::Triv { level: level.clone() }, Type::Unit { level: level.clone() }, level)))
    }

    /// A name, elaborated where the `by` is. Elaboration may leave notes and
    /// dependencies behind; a failed one is rolled back.
    fn resolve_request(&self, run: &mut Run, name: &str, span: Span) -> Result<u64, String> {
        if !is_name(name) {
            return Err(format!("`{name}` is not a name"));
        }
        let root = &run.scopes[0].cx;
        if !root.names.iter_inner().any(|n| n == name) {
            // A qualified key, as `name_of` spells one, denotes its
            // declaration wherever its module is in the import closure, as
            // for `Lookup`: a registered set of laws (a `SimpSet`) reaches a
            // `by` through modules that need not import the lemma's.
            let reached = crate::names::split_qual(name)
                .filter(|(module, base)| self.names.reaches(module) && self.names.declares(module, base))
                .and_then(|_| self.names.global(name))
                .and_then(|info| self.raw_global_at(info.abs as usize));
            if let Some((term, ty, level)) = reached.or_else(|| self.raw_global(name)) {
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
        // A qualified key, as `name_of` spells one, denotes its declaration
        // wherever its module is in the import closure: a registered table
        // (docs/metaprogramming/registered-values-design.md) reaches a `by` through the
        // modules its client imports, which need not include the lemma's.
        if let Some((module, base)) = crate::names::split_qual(name)
            && self.names.reaches(module)
        {
            if let Some(ind) = self.types.inductive(name) {
                return Ok(run.global_ref(GlobalKey::Type(ind.tag)));
            }
            if self.names.declares(module, base)
                && let Some(info) = self.names.global(name)
            {
                return Ok(run.global_ref(GlobalKey::At(info.abs as usize)));
            }
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
            run.add_hole(Hole { home: at, sol: None });
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
    /// `goal` stands for, in its scope (docs/native/facts-on-demand-design.md §4).
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
        run.add_hole(Hole { home, sol: None });
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
        let GlobalBinding::Tm { ctx, ty, level, .. } = world.bindings.get(abs)? else {
            return None;
        };
        if !ctx.entries.is_empty() || matches!(**ty, Type::UPi { .. }) {
            return None;
        }
        let var = world.reference(abs)?;
        let head = Term::GlobalTm { var, subst: LocalSubst::id(&LocalCtx::nil()) };
        Some((head, ty.shift_global(var.rescope()), level.clone()))
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
                Term::GlobalTm { var, .. } if var.innermost(m).is_some() => HeadView::Hole,
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
            let Some(targs) = Inductives(self).display_targs(&run.scopes[at].cx, ty, &ind) else {
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
            // `[A; n]`: the fixed array's former by the kernel's name, on
            // its element type and its length, whether the type is held as
            // the former or as the decoding of its code.
            Type::Vec { level, elem, len } => {
                let a = run.issue(at, Held::Type((**elem).clone(), level.clone()));
                let n = run.issue(at, Held::Term((**len).clone(), Type::Nat, Level::Zero));
                HeadView::Global(run.global_ref(GlobalKey::Builtin("Vec")), "Vec".into(), vec![a, n])
            }
            Type::El { tm, .. } if matches!(**tm, Term::TmVec { .. }) => {
                let Term::TmVec { level, elem, len } = &**tm else { unreachable!() };
                let a = run.issue(at, Held::Type(Type::El { level: level.clone(), tm: elem.clone() }, level.clone()));
                let n = run.issue(at, Held::Term((**len).clone(), Type::Nat, Level::Zero));
                HeadView::Global(run.global_ref(GlobalKey::Builtin("Vec")), "Vec".into(), vec![a, n])
            }
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
        let mut code = self.gen_ref(crate::gendefs::GenDef::TyCodeFn(ind.tag))?;
        for j in 0..m {
            let meta = Term::GlobalTm { var: GlobalVar::index(j), subst: LocalSubst::id(&cx.gamma) };
            code = Term::AppAt { fun: Rc::new(code), arg: Rc::new(meta) };
        }
        let template = Type::El { level: level.clone(), tm: Rc::new(code) };
        // Spelled applied, `El(C#tycode_fn ā)`, the arguments are read off
        // the spine: unifying the inline lowering would meet a value
        // argument applied and uncontracted (`Exists(P)`'s `El(P(witness))`,
        // a β-redex against the template's `?P(witness)`), and leave it
        // unsolved.
        let applied = match ty {
            Type::El { tm, .. } => match self.gen_app_of(tm) {
                Some((crate::gendefs::GenDef::TyCodeFn(tag), args)) if tag == ind.tag && args.len() == m as usize => Some(args),
                _ => None,
            },
            _ => None,
        };
        let sols = match applied {
            Some(args) => args.into_iter().map(Sol::Solved).collect::<Vec<_>>(),
            None => {
                let inline = self.unspell_here(&template)?;
                let mut sols = vec![Sol::Unsolved; m as usize];
                AppUnify(self).unify_root(&cx, &inline, ty, m, &mut sols, &[], Span { start: 0, end: 0 });
                if sols.iter().any(|s| s.solved().is_none()) {
                    applied_values(&cx, &inline, ty, m, 0, &mut sols);
                }
                let solved = crate::unification::zonked(&inline, m, &sols)?;
                if !self.conv_types(&cx, &solved, ty, level) {
                    return None;
                }
                sols
            }
        };
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
        let Some((record, name)) = self.field_read_parts(&run.scopes[at].cx, fun) else {
            return if args.is_empty() { self.view_payload_field(run, at, t) } else { None };
        };
        let (rty, rlevel) = self.kernel_type(run, at, record)?;
        let r = run.issue_shared(at, record, rty, rlevel);
        let mut handles = Vec::with_capacity(args.len());
        for a in args {
            let (ty, level) = self.kernel_type(run, at, a)?;
            handles.push(run.issue_shared(at, a, ty, level));
        }
        Some(HeadView::Field(r, name, handles))
    }

    /// A field of a constructor's payload, as a `match` arm reads it: the
    /// constructor's encoding is the tag then its fields, so field `k` is
    /// `fst` of `k + 1` `snd`s of the arm's payload local. Shown as a field
    /// read of the local named by the field's number (`0`, `1`, …), which no
    /// declared field name is.
    fn view_payload_field(&self, run: &mut Run, at: usize, t: &Term) -> Option<HeadView> {
        let (true, mut pair) = crate::spelling::proj_of(t)? else {
            return None;
        };
        let mut entry = 0usize;
        while let Some((false, inner)) = crate::spelling::proj_of(pair) {
            entry += 1;
            pair = inner;
        }
        let idx = entry.checked_sub(1)?;
        if !matches!(&**pair, Term::Var(_)) {
            return None;
        }
        let (pty, plevel) = self.kernel_type(run, at, pair)?;
        let payload = run.issue_shared(at, pair, pty, plevel);
        Some(HeadView::Field(payload, idx.to_string(), Vec::new()))
    }

    fn view_term(&self, run: &mut Run, at: usize, t: &Term) -> HeadView {
        // A type held as a term, `¬(a = b)`'s argument: the code of an
        // equation or a function type is shown as the type it decodes to.
        match t {
            Term::TmId { level, ty: carrier, lhs, rhs } => {
                let carrier = Type::El { level: level.clone(), tm: Rc::clone(carrier) };
                let l = run.issue(at, Held::Term((**lhs).clone(), carrier.clone(), level.clone()));
                let r = run.issue(at, Held::Term((**rhs).clone(), carrier, level.clone()));
                return HeadView::Eq(l, r);
            }
            Term::TmPi { dom_level, dom, .. } => {
                let dom = Type::El { level: dom_level.clone(), tm: Rc::clone(dom) };
                return HeadView::Pi(run.issue(at, Held::Type(dom, dom_level.clone())));
            }
            _ => {}
        }
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
            AppUnify(self).unify_root(cx, &pat, target, n, &mut sols, &slot_tys, span);
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
            subst = subst.extended(Rc::new(Term::GlobalTm { var: GlobalVar::index(j), subst: LocalSubst::id(&cx.gamma) }));
        }
        ty.shift_global(n).apply_local(&subst)
    }

    /// Fill a match's class parameters as a call fills its constraint
    /// arguments (`docs/language/classes/operation-indexed-classes-design.md` §5). With a
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
            let inline = self.unspell_here(&pat).unwrap_or_else(|| pat.clone());
            let mut fitting = 0;
            let mut found = false;
            for (goal, glvl) in dicts.goals(self, cx, &ind, span).iter() {
                let mut trial = sols.to_vec();
                let slot_tys = slot_tys.get_or_insert_with(|| Self::match_slot_tys(cx, doms, n));
                AppUnify(self).unify_root(cx, &inline, goal, n, &mut trial, slot_tys, span);
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
                // A type where a term is expected stands for its code, of
                // the universe at its level (a motive's body, `λ w => B(w)`).
                (s, Held::Type(ty, level)) => match crate::code::code_of(&ty) {
                    Some(c) => Ok(Reified {
                        term: run.lift(s, at, |k| c.shift_local(k))?,
                        ty: Type::Ty(level.clone()),
                        level: Level::succ(level),
                    }),
                    None => Err(Fault::Ill(format!(
                        "handle {h} stands for the type `{}`, which has no code and is not a term",
                        self.shown_ty(run, s, &ty)
                    ))),
                },
                (s, Held::Term(term, ty, level)) => {
                    let (s, term, ty) = if run.encloses(s, at) { (s, term, ty) } else { run.strengthened(s, at, &term, &ty)? };
                    Ok(Reified { term: run.lift(s, at, |k| term.shift_local(k))?, ty: run.lift(s, at, |k| ty.shift_local(k))?, level })
                }
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
                    // A declared type stands for its code: the code itself
                    // where it takes no parameters, so `AsType(Global(g))`
                    // is the type a name found by `Lookup` declares, and
                    // the code's function of its parameters where it has
                    // some, which `App` applies.
                    GlobalKey::Type(tag) => GeneratedDefs(self).type_code_term(tag),
                    GlobalKey::Builtin(_) => None,
                };
                let Some((term, ty, level)) = found else {
                    return Err(Fault::Ill(format!("global {g} is a kernel former or a type with no code, not a term")));
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
                    level: Level::max(dom_level, b.level),
                })
            }
        }
    }

    /// The surface term a tactic was handed as `h` ([`Quoted::Surface`]),
    /// checked at `expected`, a type of scope `at` in the current world: the
    /// type of the place the tactic's result puts it. It is elaborated in
    /// the goal's context, as it was written there, so `expected` must
    /// mention no hole and no local the tactic introduced. β-redexes a
    /// motive's application left (`P(a, b)` with `P` a `λ`) are contracted
    /// first, so the term's binders read as the goal does. A failure is the
    /// term's own error, which the run reports as itself if it fails.
    fn check_surface(&self, run: &mut Run, h: u64, expected: &Type, level: &Level, at: usize) -> Result<Term, Fault> {
        let e = run.surfaces.get(&h).cloned().expect("a surface handle");
        let Some(ty) = run.committed_ty(expected) else {
            return Err(Fault::Ill("a term handed over as written stands where the expected type mentions a hole nothing has solved".into()));
        };
        let d = (run.len(at) - run.len(0)) as u32;
        let Some(ty) = crate::unification::strengthen_ty(&run.scopes[0].cx.gamma, &ty, d) else {
            return Err(Fault::Ill(
                "a term handed over as written stands where the expected type mentions a local the tactic introduced".into(),
            ));
        };
        let ty = contract_redexes(&ty);
        let cx = run.scopes[0].cx.clone();
        match self.elab_check(&cx, &e, &ty, level) {
            Ok(term) => Ok(term.shift_local(d).shift_global(run.world() as u32)),
            Err(failure) => {
                let msg = match &failure {
                    crate::ElabError::Elab { msg, .. } => msg.clone(),
                    _ => "it does not elaborate".to_string(),
                };
                if run.surface_error.is_none() {
                    run.surface_error = Some(failure);
                }
                Err(Fault::Ill(format!("a term handed over as written does not check at its place: {msg}")))
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
        let surface = match a {
            RExpr::Hd(h) if run.surfaces.contains_key(h) => Some(*h),
            _ => None,
        };
        let (fun, dom, cod, arg) = if let Some(h) = surface {
            // A term handed over as written: checked at the domain.
            let term = self.check_surface(run, h, &dom, &dom_level, at)?;
            (f.term, dom, cod, term)
        } else if matches!(a, RExpr::Blank) {
            // An argument left to inference: a hole at the domain,
            // at this scope, which the rest of the `Expr` solves.
            run.add_hole(Hole { home: at, sol: None });
            let hole = run.occurrence(run.world() - 1);
            (f.term.shift_global(1), Rc::new(dom.shift_global(1)), Rc::new(cod.shift_global(1)), hole)
        } else {
            let a = self.reify(run, a, at)?;
            let k = run.world() as u32 - m;
            let (fun, dom, cod) = (f.term.shift_global(k), Rc::new(dom.shift_global(k)), Rc::new(cod.shift_global(k)));
            if !a.level.equiv(&dom_level) || !self.same_ty(run, at, &a.ty, &dom, &dom_level)? {
                // A comparison that ran out of fuel is not a mismatch: say so,
                // and name the budget, rather than spell two types that may
                // well be convertible (issues/runtime-fn-caller-agreement-fuel.md).
                if a.level.equiv(&dom_level) && self.ty_conv_out_of_fuel(run, at, &a.ty, &dom, &dom_level) {
                    return Err(Fault::Ill(format!(
                        "an argument's type could not be compared with the expected type within the conversion budget \
                         ({} steps): the comparison ran out of fuel, which is not a mismatch",
                        self.policy.fuel
                    )));
                }
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
                let level = Level::max(dom_level.clone(), cod_level.clone());
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
            level = Level::max(l.clone(), level);
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
    ///
    /// `Branches(e, goal)` (`plain`) is the same split by a plain `match`:
    /// no equation, and refused where the goal mentions `e`.
    fn cases_request(&self, run: &mut Run, e: &RExpr, goal: u64, plain: bool) -> Result<SplitView, Fault> {
        let at = run.join(run.scope_of(e)?, run.held(goal)?.0)?;
        let (_, goal_ty, lvl) = self.committed_goal(run, goal, Some(at), if plain { "Branches" } else { "Cases" })?;
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
        if plain && goal_ty.abstract_local_with_all(&[(scrut.clone(), Term::Var(LocalVar(0)))]).is_some() {
            return Err(Fault::Ill("`Branches` splits only a goal that does not mention its scrutinee: `Cases` splits the rest".into()));
        }
        let mut pairs = Vec::new();
        // Each side searched under its own budget: a side whose calls unfold
        // far without the test (`emit(…).holds()` beside the program's
        // verdict) would otherwise spend the search before the side that
        // holds it.
        match &goal_ty {
            Type::Id { lhs, rhs, .. } => {
                for side in [lhs, rhs] {
                    let mut budget = 256;
                    crate::goal_combinators::co_occurrences(self, &cx, side, &scrut, &scrut, &mut budget, &mut pairs);
                }
            }
            Type::El { tm, .. } => {
                for arg in crate::spelling::app_spine(tm).1 {
                    let mut budget = 256;
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
        let skeleton = if plain {
            Skeleton::Branches { scrut, ty, level: r.level, motive, arms }
        } else {
            Skeleton::Cases { scrut, ty, level: r.level, motive, equation, arms }
        };
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
        let base_aliases = cx.aliases.len();
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
            // The arm's field aliases, each shifted from the depth it was
            // bound at to the branch's.
            let fields: Vec<_> = (base_aliases..bcx.aliases.len())
                .filter_map(|i| bcx.aliases.get(i))
                .map(|a| {
                    let by = (len - a.depth) as u32;
                    (a.term.shift_local(by), a.ty.shift_local(by), a.level.clone())
                })
                .collect();
            run.scopes.push(Scope { parent: Some(at), cx: bcx, world: 0, locals });
            let locals = shown
                .into_iter()
                .map(|(id, name, ty, level)| LocalView { id, name, ty: run.issue(scope, Held::Type(ty, level)) })
                .collect();
            let fields = fields.into_iter().map(|(t, ty, level)| run.issue(scope, Held::Term(t, ty, level))).collect();
            let goal = run.issue(scope, Held::Type(ty, level));
            branches.push((scope, goal));
            views.push(BranchView { locals, goal, fields });
        }
        run.splits.push(Rc::new(Split { at, goal, lvl, skeleton, branches }));
        Ok(SplitView { id: (run.splits.len() - 1) as u64, branches: views })
    }

    /// Elaborate a split's skeleton at its goal with its leaves doing what
    /// `leaves` says, and hand back what they did.
    fn build(&self, cx: &Cx, skeleton: &Skeleton, goal: &Type, lvl: &Level, leaves: Leaves, span: Span) -> (R<Term>, Leaves) {
        let state = Rc::new(RefCell::new(leaves));
        let built = self.scoped_cell(|s| &s.host_leaves, Some(Rc::clone(&state)), || match skeleton {
            Skeleton::Cases { scrut, ty, level, motive, equation, arms } => Inference(self).elab_convoy(
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
            Skeleton::Branches { scrut, ty, level, motive, arms } => crate::matching::Routes(self).elab_match(
                cx,
                heather_syntax::MatchForm::Match,
                true,
                arms,
                scrut.clone(),
                ty,
                level,
                motive.clone(),
                lvl.clone(),
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
            Leaves::Member { fills, psi, checked } => match fills.get(k) {
                Some((Held::Term(t, ty, _), n)) if *n == cx.gamma.len() => {
                    let by = (self.goal_psi().bindings.len() - *psi) as u32;
                    if *checked && !self.conv_types(cx, &ty.shift_global(by), expected, lvl) {
                        return err("a generator registers a value under a type that is not the value's type", span);
                    }
                    Ok(t.shift_global(by))
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
            Leaves::Member { fills, psi, .. } => match fills.get(k) {
                Some((Held::Type(t, l), n)) if *n == cx.gamma.len() => {
                    Ok((t.shift_global((self.goal_psi().bindings.len() - *psi) as u32), l.clone()))
                }
                _ => err("a generated declaration's type was elaborated in another context than it was built in", span),
            },
            _ => err("a generated declaration's type outside its declaration", span),
        }
    }
}

/// The host interface's part of the elaborator that writes: prefixed and tactic declarations.
pub(crate) struct HostMut<'e>(pub(crate) &'e mut Elaborator);

impl std::ops::Deref for HostMut<'_> {
    type Target = Elaborator;
    fn deref(&self) -> &Elaborator {
        self.0
    }
}

impl std::ops::DerefMut for HostMut<'_> {
    fn deref_mut(&mut self) -> &mut Elaborator {
        self.0
    }
}

impl HostMut<'_> {
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
        let (members, psi) = Host(self).run_generator(&g.generator, &label, g.span)?;
        self.publish_members(&members, psi, &label, g.span)
    }

    /// Publish a generator's checked group, every member or none.
    fn publish_members(&mut self, members: &[Member], psi: usize, label: &str, span: Span) -> R<()> {
        self.session_transaction(|me| {
            for m in members {
                HostMut(me).publish_member(m, psi, span).map_err(|e| match e {
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
    /// `P(args) def x = e;` (docs/metaprogramming/value-definitions-design.md §3). The
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
        let prefix = prefix_name(&p.generator);
        // `register def x: T = e;`: the built-in prefix, unless a generator of
        // that name is in scope (docs/metaprogramming/registered-values-design.md).
        if prefix == "register"
            && matches!(p.generator.kind, ExprKind::Var(_))
            && !matches!(self.resolve_name(&prefix), crate::NameRes::Found(_))
        {
            return self.elab_registered_def(d);
        }
        let form = if d.value { "def" } else if d.kind == heather_syntax::ast::DeclKind::Theorem { "theorem" } else { "fn" };
        let label = format!("{prefix} {form} {}", d.name);
        if !matches!(self.resolve_name(&prefix), crate::NameRes::Found(_)) {
            return err(
                format!(
                    "`{prefix}` is not a generator in scope: a name before `{form}` is a \
                     generator, a function returning `tactic::Tac<List<tactic::Decl>>` \
                     (docs/metaprogramming/value-definitions-design.md §3)"
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
        let generator = prefix_call(&p.generator, handed);
        self.session_transaction(|me| {
            if !d.value {
                // A `for` over words in the body is lifted as a counted
                // `mut self` method (crates/elab/src/loops.rs), declared
                // under the same prefix: its generator runs over each
                // before the declaration's own, which calls them.
                let outer = me.scope.loop_methods.replace(Vec::new());
                let elaborated = me.elab_decl(d);
                let methods = std::mem::replace(&mut me.scope.loop_methods, outer).unwrap_or_default();
                elaborated?;
                for m in methods {
                    let mlabel = format!("{prefix} fn {m}");
                    let call = prefix_call(&p.generator, vec![Expr { kind: ExprKind::Str(m.clone()), span: d.span }]);
                    let (members, psi) = Host(me).run_generator(&call, &mlabel, p.span).map_err(|e| match e {
                        crate::ElabError::Elab { msg, span } => crate::ElabError::Elab {
                            msg: format!("`{label}`: its loop, lifted as `{m}`, is refused by `{prefix}`: {msg}"),
                            span,
                        },
                        other => other,
                    })?;
                    HostMut(me).publish_members(&members, psi, &mlabel, p.span)?;
                }
            }
            // A prefix's call is `P(name, args)` or `P(name, value, args)`,
            // which the refusal says, since the writer did not spell it.
            let convention = if d.value {
                format!("a generator prefixing a `def` is called as `{prefix}(name, value, …)`")
            } else {
                format!("a generator prefixing a `{form}` is called as `{prefix}(name, …)`")
            };
            let (members, psi) = Host(me).run_generator(&generator, &label, p.span).map_err(|e| match e {
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
            HostMut(me).publish_members(&members, psi, &label, p.span)
        })
    }

    /// `P record T { … }` or `P(args) record T { … }`
    /// (docs/metaprogramming/value-definitions-design.md §3.5). The record is **consumed**:
    /// declared as written, and then the generator is called with its name
    /// in front of the written arguments, `P("T", args)`, and run as
    /// `generate` runs its generator. A generator reaches the type from the
    /// name by `lookup` and `as_type(Global(g))`. One transaction: where the
    /// generator fails, the record is not declared either.
    pub(crate) fn elab_prefixed_record(&mut self, p: &heather_syntax::ast::PrefixedRecordItem) -> R<()> {
        use heather_syntax::ast::ExprKind;
        let prefix = prefix_name(&p.generator);
        let label = format!("{prefix} record {}", p.record.name);
        if !matches!(self.resolve_name(&prefix), crate::NameRes::Found(_)) {
            return err(
                format!(
                    "`{prefix}` is not a generator in scope: a name before `record` is a \
                     generator, a function returning `tactic::Tac<List<tactic::Decl>>` \
                     (docs/metaprogramming/value-definitions-design.md §3)"
                ),
                p.generator.span,
            );
        }
        let name = Expr { kind: ExprKind::Str(p.record.name.clone()), span: p.record.span };
        let generator = prefix_call(&p.generator, vec![name]);
        self.session_transaction(|me| {
            me.elab_inductive(&p.record)?;
            let convention = format!("a generator prefixing a `record` is called as `{prefix}(name, …)`");
            let (members, psi) = Host(me).run_generator(&generator, &label, p.span).map_err(|e| match e {
                crate::ElabError::Elab { msg, span } if !msg.starts_with(&format!("`{label}`")) => crate::ElabError::Elab {
                    msg: format!("`{label}`: the declaration's call of its generator is refused ({convention}): {msg}"),
                    span,
                },
                crate::ElabError::Elab { msg, span } if msg.contains("the generator's call is ill-typed") => {
                    crate::ElabError::Elab { msg: format!("{msg}; {convention}"), span }
                }
                other => other,
            })?;
            HostMut(me).publish_members(&members, psi, &label, p.span)
        })
    }
}

/// The name a prefix is written with: `P` of `P` or of `P(args)`.
fn prefix_name(generator: &Expr) -> String {
    use heather_syntax::ast::ExprKind;
    match &generator.kind {
        ExprKind::Var(n) => n.clone(),
        ExprKind::App { head, .. } => match &head.kind {
            ExprKind::Var(n) => n.clone(),
            _ => unreachable!("the parser writes a prefix as a name or a call of one"),
        },
        _ => unreachable!("the parser writes a prefix as a name or a call of one"),
    }
}

/// A prefix's call: what the declaration hands it, in front of the
/// arguments written.
fn prefix_call(generator: &Expr, handed: Vec<Expr>) -> Expr {
    use heather_syntax::ast::ExprKind;
    match &generator.kind {
        ExprKind::App { head, args, named, explicit, goal_oriented } => Expr {
            kind: ExprKind::App {
                head: head.clone(),
                args: handed.into_iter().chain(args.iter().cloned()).collect(),
                named: named.clone(),
                explicit: *explicit,
                goal_oriented: *goal_oriented,
            },
            span: generator.span,
        },
        _ => Expr {
            kind: ExprKind::App {
                head: Box::new(generator.clone()),
                args: handed,
                named: Vec::new(),
                explicit: false,
                goal_oriented: false,
            },
            span: generator.span,
        },
    }
}

impl Host<'_> {
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
        let mut run = Run::new(&cx, span, true);
        run.issue_quoted(quoted);
        match self.speak(&world, tree, |speaker| self.drive(&mut run, speaker)) {
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
        Ok(Member { theorem: d.theorem, value: d.value, instance, registered: d.registered.clone(), name: name.clone(), params, result: (result, level), body })
    }
}

impl HostMut<'_> {
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
                mode: Default::default(),
                span,
            })
            .collect();
        // A registered member writes its type by name, as `register def`
        // does: the registry is the type's, and the body the generator
        // built is checked against it like any body against its statement.
        let result = match &m.registered {
            Some(written) if is_name(written) => Ty { kind: TyKind::Named { name: written.clone(), args: Vec::new() }, span },
            Some(written) => return err(format!("`{}` is to be registered under `{written}`, which is not a type's name", m.name), span),
            None => leaf_ty(n),
        };
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
            result,
            decreases: None,
            depth: None,
            unfolding: Vec::new(),
            body: Block { stmts: Vec::new(), result: Box::new(leaf_expr(n + 1, span)), ons: Vec::new(), span },
            span,
        };
        let mut fills: Vec<(Held, usize)> =
            m.params.iter().enumerate().map(|(k, (_, _, t, l))| (Held::Type(t.clone(), l.clone()), k)).collect();
        let (result, level) = &m.result;
        fills.push((Held::Type(result.clone(), level.clone()), n));
        fills.push((Held::Term(m.body.clone(), result.clone(), level.clone()), n));
        let registered = m.registered.is_some();
        let state = Rc::new(RefCell::new(Leaves::Member { fills, psi, checked: registered }));
        self.scoped(|s| s.host_leaves.get_mut(), Some(state), |me| if registered { me.elab_registered_def(&decl) } else { me.elab_decl(&decl) })?;
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
        // A class named by its key (`name_of(Compile)`, `runtime::Compile`)
        // is cited on the caller's behalf, as an evidence rule is
        // (`DynamicScope::rule_citation`): its module need only be in the
        // import closure, so a module of programs need not import the
        // generator's own module to receive its instances.
        let (cited, class) = match crate::names::split_qual(class) {
            Some((_, base)) => (Some(class.clone()), base.to_string()),
            None => (None, class.clone()),
        };
        let class = &class;
        let info = self.scoped(|s| s.rule_citation.get_mut(), cited.clone(), |me| {
            Ok::<_, crate::ElabError>(me.key_of(class).and_then(|key| me.traits.class(&key).cloned()))
        })?;
        let Some(info) = info else {
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
        let state = Rc::new(RefCell::new(Leaves::Member { fills, psi, checked: false }));
        self.scoped(|s| s.host_leaves.get_mut(), Some(state), |me| {
            me.scoped(|s| s.rule_citation.get_mut(), cited, |me| ClassesMut(me).elab_instance(&decl))
        })
    }
}

impl Host<'_> {
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
    /// Each is committed as soon as it is checked: a later branch's `Blank`
    /// grows the world with a hole, and a term read before that growth
    /// would no longer address its globals in the larger world.
    fn branch_proofs(&self, run: &mut Run, split: &Split, proofs: &[RExpr]) -> Result<Vec<(Term, usize)>, Fault> {
        let mut fills = Vec::with_capacity(proofs.len());
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
            let c = run.committed_tm(&r.term).ok_or_else(|| {
                Fault::Ill(format!("branch {k}'s proof `{}` mentions a hole nothing solved", self.shown_tm(run, scope, &r.term)))
            })?;
            fills.push((c, run.len(scope)));
        }
        Ok(fills)
    }
}

impl Elaborator {
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

/// `ty` with the β-redexes of a motive's application contracted in every
/// `El` below its Π spine, and each code literal decoded: `P(a, b)` for
/// `P = λ y z => ⌜G⌝` reads as `G[a, b]`
/// (`spelling::beta_head_ty`, `inductive::decode_deep`).
fn contract_redexes(ty: &Type) -> Type {
    match ty {
        Type::Pi { dom_level, cod_level, dom, cod } => Type::Pi {
            dom_level: dom_level.clone(),
            cod_level: cod_level.clone(),
            dom: Rc::new(contract_redexes(dom)),
            cod: Rc::new(contract_redexes(cod)),
        },
        _ => {
            let t = crate::spelling::beta_head_ty(ty).unwrap_or_else(|| ty.clone());
            let t = crate::inductive::decode_deep(&t).unwrap_or(t);
            match &t {
                Type::Pi { .. } => contract_redexes(&t),
                _ => t,
            }
        }
    }
}

/// A value argument the unifier left unsolved, read where the template
/// applies it: the template's `El(?j(a))` against the type's `El(F(a))` at
/// the same position of the lowering, `F` the argument once it mentions no
/// binder the lowering crossed. `Exists(P)` lowers to
/// `Σ(tag). Σ(A). Σ(El(P(witness))). Unit` with the predicate applied and
/// not contracted, which the unifier does not invert. The caller's
/// conversion check of the template at what was read is the soundness check.
fn applied_values(cx: &Cx, template: &Type, ty: &Type, m: u32, crossed: u32, sols: &mut [Sol]) {
    match (template, ty) {
        (
            Type::Sigma { fst: a, snd: b, .. },
            Type::Sigma { fst: c, fst_level, snd: d, .. },
        )
        | (
            Type::Pi { dom: a, cod: b, .. },
            Type::Pi { dom: c, dom_level: fst_level, cod: d, .. },
        ) => {
            applied_values(cx, a, c, m, crossed, sols);
            let mut below = cx.clone();
            below.push("_".into(), (**c).clone(), fst_level.clone());
            applied_values(&below, b, d, m, crossed + 1, sols);
        }
        (Type::Sum { lhs: a, rhs: b, .. }, Type::Sum { lhs: c, rhs: d, .. }) => {
            applied_values(cx, a, c, m, crossed, sols);
            applied_values(cx, b, d, m, crossed, sols);
        }
        (Type::El { tm: t, .. }, Type::El { tm: u, .. }) => {
            let Some((head, arg)) = crate::spelling::app_of(t) else { return };
            let Term::GlobalTm { var, .. } = &**head else { return };
            let Some(j) = var.as_index().filter(|&j| j < m) else { return };
            if sols[j as usize].solved().is_some() {
                return;
            }
            let Some((fun, at)) = crate::spelling::app_of(u) else { return };
            if arg != at {
                return;
            }
            if let Some(f) = crate::unification::strengthen_tm(&cx.gamma, fun, crossed) {
                sols[j as usize] = Sol::Solved(Rc::new(f));
            }
        }
        _ => {}
    }
}

/// The arms of a `match`'s `Case` tree at node `j` of its type's sum
/// (`sum_layout`), `t` scoped under `depth` binders the outer `Case`s'
/// sides bound: each constructor's arm as a function of its payload, in
/// the `match`'s own context. An inner `Case` is on its parent side's
/// binder, and an arm mentions none of those binders (a `match` whose
/// motive does not read the scrutinee); anything else is refused.
fn case_tree_arms(layout: &crate::sum_layout::Layout, j: usize, t: &Term, depth: u32, found: &mut [Option<Term>]) -> Result<(), Fault> {
    let Term::Case { lhs, rhs, lhs_level, rhs_level, motive_level, case_l, case_r, scrut, .. } = t else {
        return Err(Fault::Ill("a `match` whose inner case is not a `match`".into()));
    };
    if depth > 0 && **scrut != Term::Var(LocalVar(0)) {
        return Err(Fault::Ill("a `match` whose inner case is on something other than its side's payload".into()));
    }
    let node = *layout.node(j);
    for (child, dom, dom_level, case) in [(node.lhs, lhs, lhs_level, case_l), (node.rhs, rhs, rhs_level, case_r)] {
        match child {
            crate::sum_layout::Child::Leaf(k) => {
                let lam = Term::Lam { dom_level: dom_level.clone(), cod_level: motive_level.clone(), dom: Rc::clone(dom), body: Rc::clone(case) };
                let lam = strengthened_by(&lam, depth)
                    .ok_or_else(|| Fault::Ill("an arm of a `match` reads the payload of a case around it".into()))?;
                found[k] = Some(lam);
            }
            crate::sum_layout::Child::Node(j2) => case_tree_arms(layout, j2, case, depth + 1, found)?,
        }
    }
    Ok(())
}

/// `t` with its `by` innermost free binders dropped, when it mentions none.
fn strengthened_by(t: &Term, by: u32) -> Option<Term> {
    let mut cur = t.clone();
    for _ in 0..by {
        let s = cur.inst_top(0, &Term::Zero);
        if s.shift_local(1) != cur {
            return None;
        }
        cur = s;
    }
    Some(cur)
}
