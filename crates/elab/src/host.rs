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
    pub(crate) fn force(&self, c: &'v TmClo<'v>) -> Result<Rc<Val<'v>>, String> {
        let mut ev = Eval::new(READ_FUEL, Defs::transparent_cached(self.psi, &self.cache), CtxBase::Nil, self.arena);
        ev.force(c).and_then(|v| ev.delta_whnf(v)).map_err(|_| "the host query ran out of fuel".to_string())
    }

    /// A numeral's value, a run of successors at a time; past a million it
    /// declines.
    pub(crate) fn nat(&self, c: &'v TmClo<'v>) -> Result<u64, String> {
        let mut v = self.force(c)?;
        let mut n = 0u64;
        loop {
            let next = match &*v {
                Val::Zero => return Ok(n),
                Val::Succ(p) => {
                    n += 1;
                    if n > 1_000_000 {
                        return Err("an implausible numeral".into());
                    }
                    *p
                }
                Val::NatRun { program, tail } => {
                    let remaining = 1_000_000 - n;
                    let Some(count) = ContextProgram::repetition_count_up_to(program, remaining)
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
            for d in cx.dicts.iter().rev() {
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
#[derive(Clone, Debug, PartialEq, Eq)]
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
}

impl RExpr {
    /// Every local this `Expr` names outright, not through a handle.
    fn locals(&self, out: &mut Vec<u64>) {
        match self {
            RExpr::Local(x) => out.push(*x),
            RExpr::App(f, a) => {
                f.locals(out);
                a.locals(out);
            }
            RExpr::Lam(_, body) => body.locals(out),
            RExpr::Hd(_) | RExpr::NatLit(_) | RExpr::Global(_) => {}
        }
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
    Other,
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
            out = self.arena.tm(TmClo::elim(out, Rc::new(elim)));
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

    /// A failure's message and notes.
    fn failure(&self) -> Result<Request, String> {
        let tree = self.tree;
        let msg = self.string(self.call("host_failure", vec![tree])?)?;
        let count = self.nat_of("host_note_count", vec![tree])?;
        let mut budget = READ_BUDGET;
        let mut notes = Vec::new();
        for i in 0..count {
            notes.push(self.note(self.call("host_note", vec![tree, self.lit(i)])?, &mut budget)?);
        }
        Ok(Request::Fail(msg, notes))
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
            3 => Ok(Step::Ask(self.failure()?)),
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
        Ok(self.arena.tm(TmClo::val(Rc::new(Val::Pair { ann: ann.clone(), fst, snd }))))
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
enum Held {
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

impl Fault {
    fn msg(self) -> String {
        match self {
            Fault::Protocol(m) | Fault::Ill(m) => m,
        }
    }
}

impl Run {
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
            RExpr::NatLit(_) | RExpr::Global(_) => Ok(0),
            RExpr::App(f, a) => self.join(self.scope_of(f)?, self.scope_of(a)?),
            RExpr::Lam(x, _) => {
                let (s, _) = self.local(*x)?;
                self.scopes[s].parent.ok_or_else(|| Fault::Protocol(format!("`Lam` abstracts local {x}, which the tactic did not open")))
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
        while self.trail.len() > mark {
            let j = self.trail.pop().expect("a solved hole");
            self.holes[j].sol = None;
        }
    }
}

/// One elaborated piece of a returned `Expr`.
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
    /// The quoted terms, in handle order after the goal.
    terms: RefCell<Vec<(Term, Type, Level)>>,
    /// The expression being checked without quoting, by the probe that
    /// decides whether it needs quoting at all.
    plain: Cell<Option<Span>>,
}

impl Elaborator {
    /// `by t` at `goal`: elaborate `t` as a `tactic::Tac<tactic::Expr>`, or
    /// look it up among the registered native tactics, and run it.
    pub(crate) fn run_by(&self, cx: &Cx, tactic: &Expr, goal: &Type, lvl: &Level, span: Span) -> R<Term> {
        let shown = tactic_name(tactic);
        if let heather_syntax::ast::ExprKind::Var(name) = &tactic.kind {
            if self.key_of(name).is_none() && !self.shadowed(cx, name) {
                if let Some(make) = self.native_tactics.borrow().get(name.as_str()) {
                    let mut speaker: Box<dyn NativeTactic> = make();
                    return self.run_tactic(cx, &mut speaker, &shown, goal, lvl, Vec::new(), span);
                }
            }
        }
        let world = self.goal_psi();
        let signature = |name: &str| -> R<(Term, Type)> {
            let key = format!("tactic::{name}");
            let Some(abs) = self.global_abs(&key) else {
                return err("`by` runs a tactic written against the `tactic` protocol; add `import tactic;`", span);
            };
            let len = world.bindings.len();
            let GlobalBinding::Tm { ty, .. } = &world.bindings[abs] else {
                return err(format!("`{key}` is not a term-level global"), span);
            };
            let head = Term::GlobalTm { var: GlobalVar((len - 1 - abs) as u32), subst: LocalSubst::id(&LocalCtx::nil()) };
            Ok((head, ty.shift_global((len - abs) as u32)))
        };
        let (_, tag) = signature("host_tag")?;
        let Type::Pi { dom_level, dom, .. } = tag else {
            return err("`tactic::host_tag` does not take a tactic", span);
        };
        let (quote_head, quote_ty) = signature("host_quote")?;
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
        });
        let outer = self.by_quoting.replace(Some(Rc::clone(&quoting)));
        let term = self.elab_check(cx, tactic, &dom, &dom_level);
        self.by_quoting.replace(outer);
        let term = term?;
        let Some(closed) = crate::unification::strengthen_tm(&LocalCtx::nil(), &term, cx.gamma.len() as u32) else {
            return err(
                format!(
                    "`by {shown}`: a tactic's arguments can mention the goal's locals only where it expects an \
                     `Expr`; otherwise it reaches them through the `Goal` request"
                ),
                span,
            );
        };
        let quoted = quoting.terms.borrow().clone();
        // One arena for the whole run, which keeps what it forces: each
        // resumed tree is built from closures the earlier ones forced
        // (`ValueArena::cache_tm`).
        let arena = ValueArena::new();
        let reader = Reader::new(&world, &arena);
        let tree = reader.root(closed);
        let mut speaker = Interpreted { elab: self, world: &world, reader, arena: &arena, tree, globals: Default::default() };
        self.run_tactic(cx, &mut speaker, &shown, goal, lvl, quoted, span)
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
        let Some(q) = self.by_quoting.borrow().clone() else {
            return Ok(None);
        };
        if q.plain.get() == Some(e.span) {
            q.plain.set(None);
            return Ok(None);
        }
        if !lvl.equiv(&q.level) || !self.conv_types(cx, expected, &q.expr, lvl) {
            return Ok(None);
        }
        // A bare global is quoted as itself, its implicit parameters still
        // binders of its type for `Match` to solve; inferring it would
        // insert them.
        if let heather_syntax::ast::ExprKind::Var(name) = &e.kind
            && !self.shadowed(cx, name)
            && !cx.names.iter().any(|n| n == name)
            && let Some((term, ty, level)) = self.raw_global(name)
            && !(level.equiv(&q.level) && self.conv_types(cx, &ty, &q.expr, &level))
        {
            let root = q.root.len() as u32;
            return Ok(Some(self.quoted(&q, cx, term.shift_local(root), ty.shift_local(root), level, e.span)?));
        }
        q.plain.set(Some(e.span));
        let probe = self.clone().elab_infer(cx, e);
        q.plain.set(None);
        match probe {
            Err(_) => return Ok(None),
            Ok((_, ty, level)) if level.equiv(&q.level) && self.conv_types(cx, &ty, &q.expr, &level) => return Ok(None),
            Ok(_) => {}
        }
        // Inferred for real, with quoting off: what is quoted is an
        // ordinary term, and its dependencies and notes are this
        // elaborator's.
        let outer = self.by_quoting.replace(None);
        let inferred = self.elab_infer(cx, e);
        self.by_quoting.replace(outer);
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
        Ok(Some(self.quoted(&q, cx, term, ty, level, e.span)?))
    }

    /// Record a quoted term of the goal's context and return the closed
    /// `host_quote(n)` that stands for it, weakened to `cx`.
    fn quoted(&self, q: &Quoting, cx: &Cx, term: Term, ty: Type, level: Level, span: Span) -> R<Term> {
        let n = {
            let mut terms = q.terms.borrow_mut();
            terms.push((term, ty, level));
            terms.len() as u64
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
        quoted: Vec<(Term, Type, Level)>,
        span: Span,
    ) -> R<Term> {
        let fail = |msg: String| err(format!("`by {shown}`: {msg}"), span);
        let mut run = Run {
            scopes: vec![Scope { parent: None, cx: cx.clone(), world: 0, locals: Vec::new() }],
            held: Vec::new(),
            lets: Vec::new(),
            opened: Vec::new(),
            holes: Vec::new(),
            trail: Vec::new(),
            globals: Vec::new(),
            splits: Vec::new(),
            span,
        };
        run.issue(0, Held::Type(goal.clone(), lvl.clone()));
        for (term, ty, level) in quoted {
            run.issue(0, Held::Term(term, ty, level));
        }
        self.issue_lets(cx, &mut run);
        let mut step = speaker.start();
        for answered in 0..REQUEST_BUDGET {
            let request = match step {
                Err(msg) => return fail(format!("{msg}, after {answered} requests")),
                Ok(Step::Done(e)) => return self.finish(&mut run, &e, cx, goal, lvl).or_else(|msg| fail(msg)),
                Ok(Step::Ask(request)) => request,
            };
            let answer = match request {
                Request::Goal => Answer::Goal(self.goal_view(cx, &mut run)),
                Request::Defeq(a, b) => match self.defeq(&mut run, &a, &b) {
                    Ok(same) => Answer::Bool(same),
                    Err(f) => return fail(f.msg()),
                },
                Request::Fail(msg, notes) => {
                    let rendered = match self.render_notes(&mut run, &notes) {
                        Ok(r) => r,
                        Err(f) => return fail(f.msg()),
                    };
                    return fail(format!("the tactic failed: {msg}{rendered}"));
                }
                Request::Infer(e) => match self.infer_request(&mut run, &e) {
                    Err(Fault::Protocol(msg)) => return fail(msg),
                    Err(Fault::Ill(why)) => Answer::Handle(Err(why)),
                    Ok(h) => Answer::Handle(Ok(h)),
                },
                Request::Open(h, name) => match self.open_request(&mut run, h, name) {
                    Err(Fault::Protocol(msg)) => return fail(msg),
                    Err(Fault::Ill(why)) => Answer::Opened(Err(why)),
                    Ok(o) => Answer::Opened(Ok(o)),
                },
                Request::Resolve(name) => Answer::Handle(self.resolve_request(&mut run, &name, span)),
                Request::View(h) => match self.view_request(&mut run, h) {
                    Ok(v) => Answer::Head(v),
                    Err(f) => return fail(f.msg()),
                },
                Request::Whnf(h) => match self.whnf_request(&mut run, h) {
                    Err(Fault::Protocol(msg)) => return fail(msg),
                    Err(Fault::Ill(why)) => Answer::Handle(Err(why)),
                    Ok(h) => Answer::Handle(Ok(h)),
                },
                Request::Match(ty, target) => match self.match_request(&mut run, ty, target, span) {
                    Err(Fault::Protocol(msg)) => return fail(msg),
                    Err(Fault::Ill(why)) => Answer::Match(Err(why)),
                    Ok(slots) => Answer::Match(Ok(slots)),
                },
                Request::Hole(h) => match self.hole_request(&mut run, h) {
                    Err(Fault::Protocol(msg)) => return fail(msg),
                    Err(Fault::Ill(why)) => Answer::Handle(Err(why)),
                    Ok(h) => Answer::Handle(Ok(h)),
                },
                Request::Mark => Answer::Nat(run.trail.len() as u64),
                Request::Restore(mark) => {
                    run.restore(mark as usize);
                    Answer::Unit
                }
                Request::Lookup(name) => Answer::Global(self.lookup_request(&mut run, &name)),
                Request::Cases(e, goal) => match self.cases_request(&mut run, &e, goal) {
                    Err(Fault::Protocol(msg)) => return fail(msg),
                    Err(Fault::Ill(why)) => Answer::Split(Err(why)),
                    Ok(split) => Answer::Split(Ok(split)),
                },
                Request::Constructor(goal) => match self.constructor_request(&mut run, goal) {
                    Err(Fault::Protocol(msg)) => return fail(msg),
                    Err(Fault::Ill(why)) => Answer::Split(Err(why)),
                    Ok(split) => Answer::Split(Ok(split)),
                },
                Request::Close(split, proofs) => match self.close_request(&mut run, split, &proofs) {
                    Err(Fault::Protocol(msg)) => return fail(msg),
                    Err(Fault::Ill(why)) => Answer::Handle(Err(why)),
                    Ok(h) => Answer::Handle(Ok(h)),
                },
            };
            step = speaker.resume(answer);
        }
        fail(format!("the tactic made more than {REQUEST_BUDGET} requests without finishing"))
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
            locals.push(LocalView { id: i as u64, name: cx.names.get(i).cloned().unwrap_or_else(|| "_".to_string()), ty });
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
        for (k, alias) in cx.aliases.iter().enumerate() {
            let Some(later) = cx.names.get(alias.depth..) else { continue };
            let shadowed = later.iter().any(|m| *m == alias.name)
                || cx.aliases[k + 1..].iter().any(|b| b.name == alias.name);
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
        let ty_of = |run: &Run, e: &RExpr| -> Result<Option<(Type, Level)>, Fault> {
            let RExpr::Hd(h) = e else { return Ok(None) };
            match run.held(*h)? {
                (s, Held::Type(t, l)) => Ok(Some((run.lift(s, at, |k| t.shift_local(k))?, l))),
                _ => Ok(None),
            }
        };
        let mark = run.trail.len();
        let same = match (ty_of(run, a)?, ty_of(run, b)?) {
            (Some((x, lx)), Some((y, ly))) => lx.equiv(&ly) && self.same_ty(run, at, &x, &y, &lx)?,
            (Some(_), None) | (None, Some(_)) => false,
            (None, None) => match (self.reify(run, a, at), self.reify(run, b, at)) {
                (Ok(x), Ok(y)) => self.same_tm(run, at, &x, &y)?,
                (Err(Fault::Protocol(m)), _) | (_, Err(Fault::Protocol(m))) => return Err(Fault::Protocol(m)),
                _ => false,
            },
        };
        if !same {
            run.restore(mark);
        }
        Ok(same)
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
            (None, None) => Ok(false),
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
        self.same_ty(run, at, &refl(x), &refl(y), &x.level)
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
            self.unify_under(&hcx, pat, subj, m as u32, d, &mut trial, run.span);
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
            (_, Held::Term(..)) => return Err(Fault::Ill(format!("handle {h} stands for a term, not a type"))),
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

    /// A name, elaborated where the `by` is. Elaboration may leave notes and
    /// dependencies behind; a failed one is rolled back.
    fn resolve_request(&self, run: &mut Run, name: &str, span: Span) -> Result<u64, String> {
        if !is_name(name) {
            return Err(format!("`{name}` is not a name"));
        }
        let root = &run.scopes[0].cx;
        if !root.names.iter().any(|n| n == name) {
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
        heather_kernel::typing::infer_term(oracle.world(), 0, Layer::Prog, &cx.gamma, t, self.fuel).ok()
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
        self.unify_root(&cx, &inline, ty, m, &mut sols, Span { start: 0, end: 0 });
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
        let r = run.issue(at, Held::Term((**record).clone(), rty, rlevel));
        let mut handles = Vec::with_capacity(args.len());
        for a in args {
            let (ty, level) = self.kernel_type(run, at, a)?;
            handles.push(run.issue(at, Held::Term((**a).clone(), ty, level)));
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
        if let Term::Case { scrut, .. } | Term::ElimNat { scrut, .. } = crate::goal_combinators::head_match(t) {
            return match self.kernel_type(run, at, scrut) {
                Some((ty, level)) => HeadView::Match(run.issue(at, Held::Term((**scrut).clone(), ty, level))),
                None => HeadView::Other,
            };
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
            handles.push(run.issue(at, Held::Term((**a).clone(), ty, level)));
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
                Held::Term(self.goal_oracle().whnf_term(&gamma, &t).map_err(out_of_fuel)?, ty, l)
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
        let attempt = |choice: Option<usize>| -> Result<Vec<Option<Term>>, bool> {
            let mut sols = vec![Sol::Unsolved; k];
            if let Some(c) = choice
                && !self.match_dictionaries(cx, doms, n, &mut sols, dicts, Some(c), span)
            {
                return Err(false);
            }
            self.unify_root(cx, &pat, target, n, &mut sols, span);
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
                self.unify_root(cx, &inline, goal, n, &mut trial, span);
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
            RExpr::App(f, a) => {
                let f = self.reify(run, f, at)?;
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
                let a = self.reify(run, a, at)?;
                if !a.level.equiv(&dom_level) || !self.same_ty(run, at, &a.ty, &dom, &dom_level)? {
                    return Err(Fault::Ill(format!(
                        "an argument of type `{}` where `{}` is expected",
                        self.shown_ty(run, at, &a.ty),
                        self.shown_ty(run, at, &dom)
                    )));
                }
                let arg = Rc::new(a.term);
                let ty = (*cod).clone().apply_local(&LocalSubst::id(&run.scopes[at].cx.gamma).extended(Rc::clone(&arg)));
                Ok(Reified {
                    term: Term::App { fun: Rc::new(f.term), dom_level, cod_level: cod_level.clone(), dom, cod, arg },
                    ty,
                    level: cod_level,
                })
            }
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
            let probe = self.clone();
            let (built, leaves) = probe.build(&cx, &skeleton, &goal, &lvl, Leaves::Record { placeholder, seen: vec![None; n] }, run.span);
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
                let name = bcx.names.get(p).cloned().unwrap_or_else(|| "_".to_string());
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
        let outer = self.host_leaves.replace(Some(Rc::clone(&state)));
        let built = match skeleton {
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
        };
        self.host_leaves.replace(outer);
        let leaves = state.borrow().clone();
        (built, leaves)
    }

    /// Leaf `k` of the split being elaborated (see [`Leaves`]).
    pub(crate) fn host_leaf(&self, cx: &Cx, k: usize, expected: &Type, lvl: &Level, span: Span) -> R<Term> {
        let Some(state) = self.host_leaves.borrow().clone() else {
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
        }
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
        self.native_tactics.borrow_mut().insert(name.to_string(), make);
    }
}

/// The tactic as its `by` wrote it, for messages.
fn tactic_name(e: &Expr) -> String {
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
