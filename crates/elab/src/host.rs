//! The host side of Heather tactics (docs/host-elaboration-interface-design.md).
//!
//! `by t` runs a tactic: an ordinary Heather value of `lib/std/tactic.hthr`'s
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
//! **Reading the tree.** The host never decodes `Tac`'s lowered encoding by
//! hand. Each question it asks is an application of one of the library's
//! `host_*` functions to the current tree, evaluated to a numeral, an `Expr`
//! or a `String` in the kernel's value domain (`certgen::Reader`, the
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
use heather_kernel::value::{Elim, Env, PiAnn, TmClo, TyClo, Val, ValueArena};
use heather_syntax::ast::{Expr, Span};

use crate::certgen::Reader;
use crate::context::Cx;
use crate::{err, Elaborator, R};

/// Requests one run may make before it is stopped. A tactic is library code
/// and may loop; fuel bounds each evaluation, this bounds the conversation.
const REQUEST_BUDGET: usize = 10_000;

/// Nodes of one returned `Expr`, and characters of one `String`, the host
/// will read before declining (the runaway discipline: the value is produced
/// by library code and may be arbitrarily large).
const READ_BUDGET: usize = 4096;

/// An `Expr`, as the host reads one back from a tactic.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RExpr {
    /// A handle the host issued.
    Hd(u64),
    /// A local of the goal's context, by its position from the outermost.
    Local(u64),
    App(Box<RExpr>, Box<RExpr>),
    NatLit(u64),
    /// `Lam(x, body)`: abstract the opened local `x` out of `body`.
    Lam(u64, Box<RExpr>),
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

/// A binder `Open` introduced: its local, and a handle to its body.
#[derive(Clone, Debug)]
pub struct OpenedView {
    pub local: LocalView,
    pub body: u64,
}

/// A request, as the host receives it from either kind of tactic.
#[derive(Clone, Debug)]
pub enum Request {
    Goal,
    Defeq(RExpr, RExpr),
    /// The message with its search state already rendered, one note a line.
    Fail(String),
    Infer(RExpr),
    /// A handle to a function type, and the name of the local to introduce.
    Open(u64, String),
    Resolve(String),
}

/// An answer, at the request's own kind. `Err` carries the reason a request
/// that may be refused was.
#[derive(Clone, Debug)]
pub enum Answer {
    Goal(GoalView),
    Bool(bool),
    Handle(Result<u64, String>),
    Opened(Result<OpenedView, String>),
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
            other => Err(format!("an `Expr` with tag {other}")),
        }
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
                self.call("host_opened", vec![self.lit(o.local.id), name, self.lit(o.local.ty), self.lit(o.body)])
            }
            Answer::Opened(Err(why)) => self.call("host_not_opened", vec![self.string_value(why)?]),
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
            3 => Ok(Step::Ask(Request::Fail(self.string(self.call("host_failure", vec![tree])?)?))),
            4 => {
                let mut budget = READ_BUDGET;
                Ok(Step::Ask(Request::Infer(self.expr(self.call("host_lhs", vec![tree])?, &mut budget)?)))
            }
            5 => {
                let h = self.nat_of("host_handle", vec![tree])?;
                Ok(Step::Ask(Request::Open(h, self.string(self.call("host_name", vec![tree])?)?)))
            }
            6 => Ok(Step::Ask(Request::Resolve(self.string(self.call("host_name", vec![tree])?)?))),
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
    cx: Cx,
}

/// What a handle stands for.
enum Held {
    Type(Type, Level),
    Term(Term, Type, Level),
}

/// Everything one run issued: its scopes, its handles (each in a scope),
/// and the locals `Open` introduced. Ids of the goal's own locals are their
/// positions in its context; an opened local's id is the goal's length plus
/// its index in `opened`.
struct Run {
    scopes: Vec<Scope>,
    held: Vec<(usize, Held)>,
    opened: Vec<usize>,
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

    fn held(&self, h: u64) -> Result<&(usize, Held), Fault> {
        self.held.get(h as usize).ok_or_else(|| Fault::Protocol(format!("handle {h} was not issued by this run")))
    }

    /// The scope a local belongs to and its position in that scope's context.
    fn local(&self, id: u64) -> Result<(usize, usize), Fault> {
        let root = self.len(0);
        let id = id as usize;
        if id < root {
            return Ok((0, id));
        }
        let s = *self.opened.get(id - root).ok_or_else(|| Fault::Protocol(format!("there is no local {id} in this run")))?;
        Ok((s, self.len(s) - 1))
    }

    /// The deepest scope `e` mentions, which every other one it mentions
    /// must enclose.
    fn scope_of(&self, e: &RExpr) -> Result<usize, Fault> {
        match e {
            RExpr::Hd(h) => Ok(self.held(*h)?.0),
            RExpr::Local(x) => Ok(self.local(*x)?.0),
            RExpr::NatLit(_) => Ok(0),
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

    fn issue(&mut self, scope: usize, held: Held) -> u64 {
        self.held.push((scope, held));
        (self.held.len() - 1) as u64
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
        // One arena for the whole run, keeping what it forces: each resumed
        // tree is built from closures the earlier ones forced
        // (`ValueArena::retaining`).
        let arena = ValueArena::retaining();
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
        let n = {
            let mut terms = q.terms.borrow_mut();
            terms.push((term, ty, level));
            terms.len() as u64
        };
        let (head, pi) = &q.quote;
        let Type::Pi { dom_level, cod_level, dom, cod } = &**pi else {
            return err("`tactic::host_quote` does not take a handle", e.span);
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
        Ok(Some(closed.shift_local(cx.gamma.len() as u32)))
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
        let mut run = Run { scopes: vec![Scope { parent: None, cx: cx.clone() }], held: Vec::new(), opened: Vec::new() };
        run.issue(0, Held::Type(goal.clone(), lvl.clone()));
        for (term, ty, level) in quoted {
            run.issue(0, Held::Term(term, ty, level));
        }
        let mut step = speaker.start();
        for answered in 0..REQUEST_BUDGET {
            let request = match step {
                Err(msg) => return fail(format!("{msg}, after {answered} requests")),
                Ok(Step::Done(e)) => {
                    let r = match self.reify(&run, &e, 0) {
                        Ok(r) => r,
                        Err(f) => return fail(format!("the tactic's result is not a term: {}", f.msg())),
                    };
                    if !r.level.equiv(lvl) || !self.conv_types(cx, &r.ty, goal, lvl) {
                        return fail(format!(
                            "the tactic returned a proof of `{}`, not of the goal `{}`",
                            self.display_type(cx, &r.ty),
                            self.display_type(cx, goal)
                        ));
                    }
                    return Ok(r.term);
                }
                Ok(Step::Ask(request)) => request,
            };
            let answer = match request {
                Request::Goal => Answer::Goal(self.goal_view(cx, &mut run)),
                Request::Defeq(a, b) => match self.defeq(&run, &a, &b) {
                    Ok(same) => Answer::Bool(same),
                    Err(f) => return fail(f.msg()),
                },
                Request::Fail(msg) => return fail(format!("the tactic failed: {msg}")),
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
            };
            step = speaker.resume(answer);
        }
        fail(format!("the tactic made more than {REQUEST_BUDGET} requests without finishing"))
    }

    fn goal_view(&self, cx: &Cx, run: &mut Run) -> GoalView {
        let n = cx.gamma.len();
        let mut locals = Vec::with_capacity(n);
        for i in (0..n).rev() {
            let entry = cx.gamma.entries.get(i).expect("a context entry below its length");
            let ty = run.issue(0, Held::Type(entry.ty.shift_local((n - i) as u32), entry.level.clone()));
            locals.push(LocalView { id: i as u64, name: cx.names.get(i).cloned().unwrap_or_else(|| "_".to_string()), ty });
        }
        GoalView { target: 0, locals }
    }

    fn defeq(&self, run: &Run, a: &RExpr, b: &RExpr) -> Result<bool, Fault> {
        let at = run.join(run.scope_of(a)?, run.scope_of(b)?)?;
        let cx = &run.scopes[at].cx;
        let ty_of = |e: &RExpr| -> Result<Option<(Type, Level)>, Fault> {
            let RExpr::Hd(h) = e else { return Ok(None) };
            match run.held(*h)? {
                (s, Held::Type(t, l)) => Ok(Some((run.lift(*s, at, |k| t.shift_local(k))?, l.clone()))),
                _ => Ok(None),
            }
        };
        match (ty_of(a)?, ty_of(b)?) {
            (Some((x, lx)), Some((y, ly))) => Ok(lx.equiv(&ly) && self.conv_types(cx, &x, &y, &lx)),
            (Some(_), None) | (None, Some(_)) => Ok(false),
            (None, None) => {
                let x = self.reify(run, a, at)?;
                let y = self.reify(run, b, at)?;
                if !x.level.equiv(&y.level) || !self.conv_types(cx, &x.ty, &y.ty, &x.level) {
                    return Ok(false);
                }
                Ok(self
                    .goal_oracle()
                    .convert_term(&cx.gamma, Layer::Prog, &x.term, &y.term, &x.ty, &x.level)
                    .is_ok())
            }
        }
    }

    fn infer_request(&self, run: &mut Run, e: &RExpr) -> Result<u64, Fault> {
        let at = run.scope_of(e)?;
        let r = self.reify(run, e, at)?;
        Ok(run.issue(at, Held::Type(r.ty, r.level)))
    }

    fn open_request(&self, run: &mut Run, h: u64, name: String) -> Result<OpenedView, Fault> {
        let (at, ty) = match run.held(h)? {
            (s, Held::Type(t, _)) => (*s, t.clone()),
            (_, Held::Term(..)) => return Err(Fault::Ill(format!("handle {h} stands for a term, not a type"))),
        };
        let cx = &run.scopes[at].cx;
        let pi = self
            .goal_oracle()
            .whnf_type(&cx.gamma, &ty)
            .map_err(|_| Fault::Ill("ran out of fuel exposing a function type".into()))?;
        let Type::Pi { dom_level, cod_level, dom, cod } = pi else {
            return Err(Fault::Ill(format!("`{}` is not a function type", self.display_type(cx, &ty))));
        };
        let mut inner = cx.clone();
        inner.push(name.clone(), (*dom).clone(), dom_level.clone());
        run.scopes.push(Scope { parent: Some(at), cx: inner });
        let scope = run.scopes.len() - 1;
        run.opened.push(scope);
        let id = (run.len(0) + run.opened.len() - 1) as u64;
        let ty = run.issue(at, Held::Type((*dom).clone(), dom_level));
        let body = run.issue(scope, Held::Type((*cod).clone(), cod_level));
        Ok(OpenedView { local: LocalView { id, name, ty }, body })
    }

    /// A name, elaborated where the `by` is. Elaboration may leave notes and
    /// dependencies behind; a failed one is rolled back.
    fn resolve_request(&self, run: &mut Run, name: &str, span: Span) -> Result<u64, String> {
        let valid = !name.is_empty()
            && name.split("::").all(|part| {
                let mut cs = part.chars();
                cs.next().is_some_and(|c| c.is_alphabetic() || c == '_') && cs.all(|c| c.is_alphanumeric() || c == '_')
            });
        if !valid {
            return Err(format!("`{name}` is not a name"));
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

    /// A returned `Expr` as a kernel term of scope `at`, built directly:
    /// handles, locals and literals are terms already, an application is
    /// formed against its head's Π after a conversion check of the argument,
    /// and `Lam` abstracts an opened local of `at`'s child. No name is
    /// resolved and nothing is re-parsed (design §4.1).
    fn reify(&self, run: &Run, e: &RExpr, at: usize) -> Result<Reified, Fault> {
        let cx = &run.scopes[at].cx;
        match e {
            RExpr::Hd(h) => match run.held(*h)? {
                (_, Held::Type(ty, _)) => Err(Fault::Ill(format!(
                    "handle {h} stands for the type `{}`, which is not a term",
                    self.display_type(&run.scopes[run.held(*h)?.0].cx, ty)
                ))),
                (s, Held::Term(term, ty, level)) => Ok(Reified {
                    term: run.lift(*s, at, |k| term.shift_local(k))?,
                    ty: run.lift(*s, at, |k| ty.shift_local(k))?,
                    level: level.clone(),
                }),
            },
            RExpr::Local(x) => {
                let (s, i) = run.local(*x)?;
                if !run.encloses(s, at) {
                    return Err(Fault::Protocol(format!("local {x} is used outside its binder")));
                }
                let n = cx.gamma.len();
                let entry = cx.gamma.entries.get(i).expect("a local of an enclosing scope");
                Ok(Reified {
                    term: Term::Var(LocalVar((n - 1 - i) as u32)),
                    ty: entry.ty.shift_local((n - i) as u32),
                    level: entry.level.clone(),
                })
            }
            RExpr::NatLit(k) => Ok(Reified { term: crate::inductive::nat_lit(*k as usize), ty: Type::Nat, level: Level::Zero }),
            RExpr::App(f, a) => {
                let f = self.reify(run, f, at)?;
                let pi = self
                    .goal_oracle()
                    .whnf_type(&cx.gamma, &f.ty)
                    .map_err(|_| Fault::Ill("ran out of fuel exposing a function type".into()))?;
                let Type::Pi { dom_level, cod_level, dom, cod } = pi else {
                    return Err(Fault::Ill(format!("`{}` is applied but is not a function", self.display_type(cx, &f.ty))));
                };
                let a = self.reify(run, a, at)?;
                if !a.level.equiv(&dom_level) || !self.conv_types(cx, &a.ty, &dom, &dom_level) {
                    return Err(Fault::Ill(format!(
                        "an argument of type `{}` where `{}` is expected",
                        self.display_type(cx, &a.ty),
                        self.display_type(cx, &dom)
                    )));
                }
                let arg = Rc::new(a.term);
                let ty = (*cod).clone().apply_local(&LocalSubst::id(&cx.gamma).extended(Rc::clone(&arg)));
                Ok(Reified {
                    term: Term::App { fun: Rc::new(f.term), dom_level, cod_level: cod_level.clone(), dom, cod, arg },
                    ty,
                    level: cod_level,
                })
            }
            RExpr::Lam(x, body) => {
                let (s, i) = run.local(*x)?;
                if run.scopes[s].parent != Some(at) || i < run.len(0) {
                    return Err(Fault::Protocol(format!("`Lam` abstracts local {x}, which is not bound here")));
                }
                let b = self.reify(run, body, s)?;
                let entry = run.scopes[s].cx.gamma.entries.get(i).expect("an opened local");
                let dom = Rc::clone(&entry.ty);
                let dom_level = entry.level.clone();
                Ok(Reified {
                    term: Term::Lam { dom_level: dom_level.clone(), cod_level: b.level.clone(), dom: Rc::clone(&dom), body: Rc::new(b.term) },
                    ty: Type::Pi { dom_level: dom_level.clone(), cod_level: b.level.clone(), dom, cod: Rc::new(b.ty) },
                    level: Level::join(dom_level, b.level),
                })
            }
        }
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
