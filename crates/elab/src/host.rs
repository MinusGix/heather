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

/// A request, as the host receives it from either kind of tactic.
#[derive(Clone, Debug)]
pub enum Request {
    Goal,
    Defeq(RExpr, RExpr),
    /// The message with its search state already rendered, one note a line.
    Fail(String),
}

/// An answer, at the request's own kind.
#[derive(Clone, Debug)]
pub enum Answer {
    Goal(GoalView),
    Bool(bool),
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

/// What a handle stands for. Round 1 issues handles to types only: the goal's
/// statement and its locals' types.
struct Handles {
    types: Vec<(Type, Level)>,
}

/// One elaborated piece of a returned `Expr`.
struct Reified {
    term: Term,
    ty: Type,
    level: Level,
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
                    return self.run_tactic(cx, &mut speaker, &shown, goal, lvl, span);
                }
            }
        }
        let Some(abs) = self.global_abs("tactic::host_tag") else {
            return err("`by` runs a tactic written against the `tactic` protocol; add `import tactic;`", span);
        };
        let world = self.goal_psi();
        let len = world.bindings.len();
        let GlobalBinding::Tm { ty, .. } = &world.bindings[abs] else {
            return err("`tactic::host_tag` is not a term-level global", span);
        };
        let Type::Pi { dom_level, dom, .. } = ty.shift_global((len - abs) as u32) else {
            return err("`tactic::host_tag` does not take a tactic", span);
        };
        let term = self.elab_check(cx, tactic, &dom, &dom_level)?;
        let Some(closed) = crate::unification::strengthen_tm(&LocalCtx::nil(), &term, cx.gamma.len() as u32) else {
            return err(
                format!(
                    "`by {shown}`: a tactic's arguments cannot mention the goal's locals yet; a tactic \
                     reaches them through the `Goal` request"
                ),
                span,
            );
        };
        // One arena for the whole run, keeping what it forces: each resumed
        // tree is built from closures the earlier ones forced
        // (`ValueArena::retaining`).
        let arena = ValueArena::retaining();
        let reader = Reader::new(&world, &arena);
        let tree = reader.root(closed);
        let mut speaker = Interpreted { elab: self, world: &world, reader, arena: &arena, tree, globals: Default::default() };
        self.run_tactic(cx, &mut speaker, &shown, goal, lvl, span)
    }

    /// The host loop: drive `speaker` to a result, answering its requests in
    /// `cx`, and check the result at `goal`.
    fn run_tactic(
        &self,
        cx: &Cx,
        speaker: &mut dyn Speaker,
        shown: &str,
        goal: &Type,
        lvl: &Level,
        span: Span,
    ) -> R<Term> {
        let fail = |msg: String| err(format!("`by {shown}`: {msg}"), span);
        let mut handles = Handles { types: vec![(goal.clone(), lvl.clone())] };
        let mut step = speaker.start();
        for answered in 0..REQUEST_BUDGET {
            let request = match step {
                Err(msg) => return fail(format!("{msg}, after {answered} requests")),
                Ok(Step::Done(e)) => {
                    let r = match self.reify(cx, &handles, &e) {
                        Ok(r) => r,
                        Err(msg) => return fail(format!("the tactic's result is not a term: {msg}")),
                    };
                    if r.level != *lvl || !self.conv_types(cx, &r.ty, goal, lvl) {
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
                Request::Goal => Answer::Goal(self.goal_view(cx, &mut handles)),
                Request::Defeq(a, b) => match self.defeq(cx, &handles, &a, &b) {
                    Ok(same) => Answer::Bool(same),
                    Err(msg) => return fail(msg),
                },
                Request::Fail(msg) => return fail(format!("the tactic failed: {msg}")),
            };
            step = speaker.resume(answer);
        }
        fail(format!("the tactic made more than {REQUEST_BUDGET} requests without finishing"))
    }

    fn goal_view(&self, cx: &Cx, handles: &mut Handles) -> GoalView {
        let n = cx.gamma.len();
        let mut locals = Vec::with_capacity(n);
        for i in (0..n).rev() {
            let entry = cx.gamma.entries.get(i).expect("a context entry below its length");
            let ty = entry.ty.shift_local((n - i) as u32);
            handles.types.push((ty, entry.level.clone()));
            locals.push(LocalView {
                id: i as u64,
                name: cx.names.get(i).cloned().unwrap_or_else(|| "_".to_string()),
                ty: (handles.types.len() - 1) as u64,
            });
        }
        GoalView { target: 0, locals }
    }

    fn defeq(&self, cx: &Cx, handles: &Handles, a: &RExpr, b: &RExpr) -> Result<bool, String> {
        match (a, b) {
            (RExpr::Hd(x), RExpr::Hd(y)) => {
                let (tx, lx) = handle(handles, *x)?;
                let (ty, ly) = handle(handles, *y)?;
                Ok(lx == ly && self.conv_types(cx, tx, ty, lx))
            }
            (RExpr::Hd(h), _) | (_, RExpr::Hd(h)) => {
                handle(handles, *h)?;
                Ok(false)
            }
            _ => {
                let x = self.reify(cx, handles, a)?;
                let y = self.reify(cx, handles, b)?;
                if x.level != y.level || !self.conv_types(cx, &x.ty, &y.ty, &x.level) {
                    return Ok(false);
                }
                Ok(self
                    .goal_oracle()
                    .convert_term(&cx.gamma, Layer::Prog, &x.term, &y.term, &x.ty, &x.level)
                    .is_ok())
            }
        }
    }

    /// A returned `Expr` as a kernel term of `cx`, built directly: locals and
    /// literals are terms already, and an application is formed against its
    /// head's Π after a conversion check of the argument. No name is resolved
    /// and nothing is re-parsed (design §4.1).
    fn reify(&self, cx: &Cx, handles: &Handles, e: &RExpr) -> Result<Reified, String> {
        match e {
            RExpr::Hd(h) => {
                let (ty, _) = handle(handles, *h)?;
                Err(format!("handle {h} stands for the type `{}`, which is not a term", self.display_type(cx, ty)))
            }
            RExpr::Local(i) => {
                let n = cx.gamma.len();
                let i = *i as usize;
                let entry = cx.gamma.entries.get(i).ok_or_else(|| format!("there is no local {i} in this goal"))?;
                Ok(Reified {
                    term: Term::Var(LocalVar((n - 1 - i) as u32)),
                    ty: entry.ty.shift_local((n - i) as u32),
                    level: entry.level.clone(),
                })
            }
            RExpr::NatLit(k) => Ok(Reified { term: crate::inductive::nat_lit(*k as usize), ty: Type::Nat, level: Level::Zero }),
            RExpr::App(f, a) => {
                let f = self.reify(cx, handles, f)?;
                let pi = self
                    .goal_oracle()
                    .whnf_type(&cx.gamma, &f.ty)
                    .map_err(|_| "ran out of fuel exposing a function type".to_string())?;
                let Type::Pi { dom_level, cod_level, dom, cod } = pi else {
                    return Err(format!("`{}` is applied but is not a function", self.display_type(cx, &f.ty)));
                };
                let a = self.reify(cx, handles, a)?;
                if a.level != dom_level || !self.conv_types(cx, &a.ty, &dom, &dom_level) {
                    return Err(format!(
                        "an argument of type `{}` where `{}` is expected",
                        self.display_type(cx, &a.ty),
                        self.display_type(cx, &dom)
                    ));
                }
                let arg = Rc::new(a.term);
                let ty = (*cod).clone().apply_local(&LocalSubst::id(&cx.gamma).extended(Rc::clone(&arg)));
                Ok(Reified {
                    term: Term::App { fun: Rc::new(f.term), dom_level, cod_level: cod_level.clone(), dom, cod, arg },
                    ty,
                    level: cod_level,
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

fn handle(handles: &Handles, h: u64) -> Result<(&Type, &Level), String> {
    handles
        .types
        .get(h as usize)
        .map(|(t, l)| (t, l))
        .ok_or_else(|| format!("handle {h} was not issued by this run"))
}

/// The tactic as its `by` wrote it, for messages.
fn tactic_name(e: &Expr) -> String {
    match &e.kind {
        heather_syntax::ast::ExprKind::Var(name) => name.clone(),
        heather_syntax::ast::ExprKind::App { head, .. } => format!("{}(…)", tactic_name(head)),
        _ => "…".to_string(),
    }
}
