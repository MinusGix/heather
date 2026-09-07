//! The **evaluator**: (syntax, environment) → weak head normal value
//! (docs/nbe-conversion-design.md §§3–6).
//!
//! This is the environment machine that replaces the term rewriter's
//! substitute-and-re-reduce loop on the conversion path. It decides the same
//! relation `reduce.rs` transcribes — ch. 06's untyped weak-head reduction
//! plus δ — but an eliminator's β **extends an environment** instead of
//! copying a branch, which is what changes the exponent of
//! `issues/whnf-sharing-term-growth.md`.
//!
//! It is **not wired into `conv.rs`**: stage 1 of the round lands the domain
//! and the machine, differentially tested against the rewriter
//! (`tests/eval_differential.rs`); stage 2b switches conversion over.
//!
//! What it shares rather than transcribes:
//!
//! - [`crate::reduce::beta_elim_ty`] / [`beta_elim_tm`] — the ~1300-line code
//!   recursor β. The evaluator hands the box's payload to the *existing*
//!   function, receives the fired branch as **syntax**, and evaluates it. The
//!   56 branch telescopes are not written down a sixth time.
//! - [`crate::term::nth`] and the `elim_W`/`elim_Wf` ih λs, which are built
//!   from the same syntax `reduce.rs` builds — see [`Eval::fire_elim_w`].
//! - [`crate::reduce::step_type_delta`], for the one annotation that lives in
//!   a *different* local scope: `elim^Trm`'s type annotation, scoped in Δ
//!   (ch. 06 fixes the type-then-term reduction order).
//!
//! ## Laziness, and where it stops
//!
//! Sub-structures are [`TmClo`]/[`TyClo`] — environment plus syntax, forced
//! on demand and memoized. That is deliberate and it is what keeps the
//! machine faithful to ch. 06: weak-head reduction does not look inside
//! `su t`, an unfired branch, or an unread annotation, and neither does this.
//! A strict (children-are-values) domain would agree on every value and still
//! reduce a never-forced induction hypothesis — the shape §12 of the design
//! measured as family C.
//!
//! **Forcing is fallible everywhere** ([`Eval::force`], [`Eval::force_ty`],
//! [`Eval::apply`]): no `Deref`, no infallible accessor, no `unwrap`. And a
//! thunk that fails memoizes **nothing**, so re-forcing the same value graph
//! under a larger budget succeeds (design §6).
//!
//! ## Fuel
//!
//! One unit per evaluation step ch. 06 would have counted: every closure
//! application (β at `Lam`/`ULam`/`CtxLam`/`TyLam`), every eliminator fire,
//! every `El` decode, every `Vec`/`Fin` unfold, every δ-unfold. Exhaustion is
//! [`OutOfFuel`] and is never a verdict.

use std::num::NonZeroU64;
use std::rc::Rc;

use crate::level::Level;
use crate::reduce::{beta_elim_ty, beta_elim_tm, step_type_delta, Defs, OutOfFuel, Rec};
use crate::subst::{GlobalEntry, GlobalSubst};
use crate::term::{
    nth, CtxBase, CtxEntries, CtxEntry, GlobalVar, LocalCtx, LocalSubst, LocalVar, Term, Type,
};
use crate::value::{
    Elim, ElimSpine, Env, Head, Lookup, TmClo, TyClo, VNeTy, VNeutral, VSubst, VTail,
    VTy, Val, ValueArena,
};
use crate::value::program::ContextProgram;

type Res<T> = Result<T, OutOfFuel>;

// ---------------------------------------------------------------------------
// Small constructors
// ---------------------------------------------------------------------------

fn neutral<'v>(
    head: Head<'v>,
    spine: ElimSpine<'v>,
    unfold: Option<&'v TmClo<'v>>,
) -> Rc<Val<'v>> {
    Rc::new(Val::Neutral(Rc::new(VNeutral { head, spine, unfold })))
}

/// An eliminator applied to something it cannot eliminate. Unreachable on
/// well-typed input — `reduce.rs` is equally stuck there — but represented
/// rather than panicked on, so no input reaches undefined behaviour.
fn stuck<'v>(arena: &'v ValueArena<'v>, head: &Rc<Val<'v>>, e: &Elim<'v>) -> Rc<Val<'v>> {
    let spine = arena.elim(ElimSpine::empty(), e.clone());
    neutral(Head::Stuck(Rc::clone(head)), spine, None)
}

/// The fold step has the exact shape
///
/// `λ m. elim_Nat ... m ... (λ l _. ih l)`.
///
/// Here `ih` is the outer fold's recursive result. This is a structural
/// homomorphism for a *pair* of matching successor contexts: one constructor
/// from each side reduces to the same fold at both predecessors. Types,
/// motives, and zero branches may be arbitrary; they remain in the original
/// eliminators and are evaluated once cancellation reaches a residual.
fn nat_step_synchronizes(step: &TmClo<'_>) -> bool {
    let Some((_, body)) = step.as_syn() else { return false };
    let Term::Lam { body, .. } = &**body else { return false };
    let Term::ElimNat { scrut, step, .. } = &**body else { return false };
    if !matches!(&**scrut, Term::Var(LocalVar(0))) {
        return false;
    }
    matches!(&**step,
        Term::App { fun, arg, .. }
            if matches!(&**fun, Term::Var(LocalVar(3)))
                && matches!(&**arg, Term::Var(LocalVar(1))))
}

/// The fold step has the exact shape `λ k ih. su^p ih` for some `p ≥ 1`:
/// the successor algebra, `p` constructors per input constructor. Over a run
/// of `c` successors it is the run of `p·c`, mapped onto the fold at the
/// tail; `Some(p)` is that count. `p = 1` (`add`) leaves the program itself
/// in place; `p = 2` is `twice`.
fn nat_step_successors(step: &TmClo<'_>) -> Option<u64> {
    let Some((_, body)) = step.as_syn() else { return None };
    let mut count = 0u64;
    let mut cur = &**body;
    while let Term::Succ(inner) = cur {
        count += 1;
        cur = &**inner;
    }
    (count >= 1 && matches!(cur, Term::Var(LocalVar(0)))).then_some(count)
}

// ---------------------------------------------------------------------------
// The machine
// ---------------------------------------------------------------------------

/// A pending reduction, in the tail position of [`Eval::drive`]'s loop.
enum Work<'v> {
    /// Already a weak head value.
    Val(Rc<Val<'v>>),
    /// `eval(t, ρ)`.
    Eval(Rc<Term>, Env<'v>),
    /// Force a 0-binder sub-structure.
    Force(&'v TmClo<'v>),
    /// Apply a closure to its pending binders' values.
    Apply(&'v TmClo<'v>, Vec<&'v TmClo<'v>>),
    /// [`Work::Apply`] at one binder — β's commonest shape, and the one that
    /// must not allocate a vector to say so.
    Apply1(&'v TmClo<'v>, &'v TmClo<'v>),
    /// Eliminate a weak head value.
    Elim(Rc<Val<'v>>, Elim<'v>),
}

/// What a value flows back into: a thunk waiting to memoize it, or an
/// elimination waiting for its head.
enum Frame<'v> {
    Memo(&'v TmClo<'v>),
    Elim(Rc<Elim<'v>>),
    /// A successor program waiting for the value its fold produced at the
    /// run's tail. A run there is merged into one program rather than left
    /// as the next fragment of a chain, so that `add`-shaped folds over
    /// literals — `p + p`, `mul(p, 2)` — build one saturated run and not
    /// one fragment per logical addition.
    ///
    /// Under conversion's δ-lazy evaluation the tail's fold is usually a
    /// *glued* neutral (`mul(2, k)` unfolded once is `add(mul(2, k-1), 2)`,
    /// whose tail is the still-glued `mul(2, k-1)`), so the frame unfolds
    /// glued heads at the tail until a run, a constructor, or a stuck
    /// neutral appears — each unfolding charged as a δ-step. `glued` keeps
    /// the first glued neutral: if the unfoldings end stuck, that is the
    /// tail conversion keeps, so an open wrapper is not normalized away.
    NatRunTail {
        program: Rc<ContextProgram<()>>,
        glued: Option<Rc<Val<'v>>>,
    },
    /// A synchronous fold (`head`, a `NatSync`) waiting for its unfolded
    /// right-hand counter; the application `app` is retried with the value
    /// that flows back in place of its argument.
    SyncArg {
        head: Rc<Val<'v>>,
        app: Rc<Elim<'v>>,
    },
}

/// An evaluation run: the shared fuel budget, the δ-environment, and the
/// **base** of the ambient local context.
///
/// The base is the one piece of Γ the machine needs beyond the environment:
/// de Bruijn indices past the environment's concrete entries name variables
/// of the abstract prefix `g` (see [`Head::BaseVar`]), and the shared β
/// helpers materialize `id_Γ`, which reads Γ's length and base and nothing
/// else. It never changes during a run: a universe or global instantiation
/// renumbers the *outer* scope back down, so the captured environment is
/// already in the post-instantiation scope, and a context variable
/// substituted by `Λ(g). t` is always freshly bound and therefore never Γ's
/// base.
pub struct Eval<'a, 'v> {
    fuel: u64,
    defs: Defs<'a>,
    base: CtxBase,
    arena: &'v ValueArena<'v>,
    /// [`Eval::drive`]'s continuation stack, kept across drives so that the
    /// common reduction step allocates nothing for it. Nested drives (a
    /// scrutinee evaluated before its elimination is built) use it as a
    /// stack of stacks: each records the height it entered at.
    frames: Vec<Frame<'v>>,
}

impl<'a, 'v> Eval<'a, 'v> {
    /// A run with `fuel` units, unfolding the definitions of `defs`, over a Γ
    /// whose base is `base`.
    pub fn new(
        fuel: u64,
        defs: Defs<'a>,
        base: CtxBase,
        arena: &'v ValueArena<'v>,
    ) -> Eval<'a, 'v> {
        Eval { fuel, defs, base, arena, frames: Vec::new() }
    }

    /// The unspent budget.
    pub fn fuel(&self) -> u64 {
        self.fuel
    }

    fn vclo(&self, value: Rc<Val<'v>>) -> &'v TmClo<'v> {
        self.arena.tm(TmClo::val(value))
    }

    fn nat_residual(
        &self,
        program: Option<Rc<ContextProgram<()>>>,
        tail: &'v TmClo<'v>,
    ) -> &'v TmClo<'v> {
        match program {
            None => tail,
            Some(program) => self.vclo(Rc::new(Val::NatRun { program, tail })),
        }
    }

    fn spend(&mut self) -> Res<()> {
        if self.fuel == 0 {
            return Err(OutOfFuel);
        }
        self.fuel -= 1;
        Ok(())
    }

    /// A Γ of the right *shape* for the shared β helpers, which read only its
    /// length and base (`reduce.rs` module doc). The entry types are never
    /// inspected, so a filler suffices — and building one is confined to the
    /// code-recursor path, which is not the hot one.
    fn scope(&self, env: &Env<'v>) -> LocalCtx {
        LocalCtx {
            base: self.base,
            entries: CtxEntries::repeat(
                CtxEntry { ty: Rc::new(Type::Nat), level: Level::Zero },
                env.len() as usize,
            ),
        }
    }

    // -- the trampoline -----------------------------------------------------

    /// Drive a piece of work to a value, keeping the machine's **tail calls
    /// off the native stack**.
    ///
    /// Every link in a reduction chain — evaluate an application, fire its β,
    /// apply the closure, evaluate the body, meet the next application — is a
    /// tail call, and a rewriter spends them in a `while` loop
    /// (`reduce.rs`'s `whnf_*`). Written as Rust recursion they would make
    /// the machine's stack depth proportional to the *number of reduction
    /// steps* rather than to the term's depth, and a divergent term would
    /// then abort the process instead of returning [`OutOfFuel`] — turning
    /// the fuel policy, which exists to make the checker total on ill-typed
    /// input, into a crash. (Measured, 2026-07-31: Ω under a 500-step budget
    /// overflowed an 8 MiB stack.)
    ///
    /// So the tail positions are *returned* as [`Work`] and spent here, and
    /// the two places a result has to flow back into something — a thunk
    /// waiting for its memo, an elimination waiting for its head — become
    /// explicit [`Frame`]s on the heap. Non-tail recursion (a scrutinee, an
    /// application's function, a type annotation) stays on the native stack,
    /// where its depth is the syntax's and the rewriter's own.
    fn drive(&mut self, start: Work<'v>) -> Res<Rc<Val<'v>>> {
        let floor = self.frames.len();
        let out = self.drive_from(start, floor);
        // An error unwinds whatever this drive had pending; a thunk that
        // never reached its frame keeps no memo (design §6).
        self.frames.truncate(floor);
        out
    }

    fn drive_from(&mut self, start: Work<'v>, floor: usize) -> Res<Rc<Val<'v>>> {
        let mut work = start;
        loop {
            work = match work {
                Work::Eval(t, env) => self.step_eval(&t, &env)?,
                Work::Elim(head, e) => self.step_elim(head, e)?,
                Work::Apply1(c, arg) => match c {
                    TmClo::Syn { env, body, .. } => {
                        Work::Eval(Rc::clone(body), env.push(self.arena, arg))
                    }
                    _ => Work::Force(c),
                },
                Work::Apply(c, args) => match c {
                    TmClo::Syn { env, body, .. } => {
                        Work::Eval(Rc::clone(body), env.extend(self.arena, &args))
                    }
                    // A closure position holding a computed value has no
                    // pending binders; it ignores them.
                    _ => Work::Force(c),
                },
                Work::Force(c) => {
                    if let Some(v) = self.arena.memo_tm(c) {
                        Work::Val(v)
                    } else {
                        match c {
                            TmClo::Val(v) => Work::Val(Rc::clone(v)),
                            TmClo::Syn { env, body, .. } => {
                                let w = Work::Eval(Rc::clone(body), *env);
                                self.frames.push(Frame::Memo(c));
                                w
                            }
                            TmClo::Elim { head, elim, .. } => {
                                let w = Work::Force(head);
                                self.frames.push(Frame::Memo(c));
                                self.frames.push(Frame::Elim(Rc::clone(elim)));
                                w
                            }
                        }
                    }
                }
                Work::Val(v) => {
                    if self.frames.len() == floor {
                        return Ok(v);
                    }
                    match self.frames.pop() {
                        None => return Ok(v),
                        // A thunk records its value only on success.
                        Some(Frame::Memo(c)) => {
                            self.arena.cache_tm(c, &v);
                            Work::Val(v)
                        }
                        Some(Frame::Elim(e)) => Work::Elim(v, (*e).clone()),
                        Some(Frame::SyncArg { head, app }) => {
                            let Elim::App { dom_level, cod_level, dom, cod, .. } = &*app else {
                                unreachable!("SyncArg stores an application")
                            };
                            let app = Elim::App {
                                dom_level: dom_level.clone(),
                                cod_level: cod_level.clone(),
                                dom: *dom,
                                cod: *cod,
                                arg: self.vclo(v),
                            };
                            Work::Elim(head, app)
                        }
                        Some(Frame::NatRunTail { program, glued }) => match &*v {
                            Val::NatRun { program: inner, tail } => {
                                Work::Val(Rc::new(Val::NatRun {
                                    program: ContextProgram::append(program, Rc::clone(inner)),
                                    tail: *tail,
                                }))
                            }
                            Val::Neutral(n) if n.unfold.is_some() => {
                                self.spend()?;
                                let unfold = n.unfold.unwrap();
                                let glued = glued.or_else(|| Some(Rc::clone(&v)));
                                self.frames.push(Frame::NatRunTail { program, glued });
                                Work::Force(unfold)
                            }
                            Val::Neutral(_) => {
                                let tail = glued.unwrap_or(v);
                                Work::Val(Rc::new(Val::NatRun { program, tail: self.vclo(tail) }))
                            }
                            _ => Work::Val(Rc::new(Val::NatRun { program, tail: self.vclo(v) })),
                        },
                    }
                }
            };
        }
    }

    // -- forcing and application -------------------------------------------

    /// Force a 0-binder sub-structure to its weak head value. Memoizes on
    /// success only.
    pub fn force(&mut self, c: &'v TmClo<'v>) -> Res<Rc<Val<'v>>> {
        self.drive(Work::Force(c))
    }

    /// [`Eval::force`] for types.
    pub fn force_ty(&mut self, c: &'v TyClo<'v>) -> Res<Rc<VTy<'v>>> {
        if let Some(v) = self.arena.memo_ty(c) {
            return Ok(v);
        }
        let v = match c {
            TyClo::Val(v) => Rc::clone(v),
            TyClo::Syn { env, body, .. } => {
                let (env, body) = (*env, Rc::clone(body));
                self.eval_ty(&body, &env)?
            }
            TyClo::Vec { level, elem, len, .. } => {
                let (level, elem, len) = (*level, *elem, *len);
                let lv = self.force(len)?;
                self.vec_ty(level, elem, &lv)?
            }
            TyClo::El { level, tm, .. } => {
                let (level, tm) = (*level, *tm);
                let v = self.force(tm)?;
                self.decode(level, &v)?
            }
        };
        self.arena.cache_ty(c, &v);
        Ok(v)
    }

    /// Apply a closure to its pending binders' values, `args[0]` outermost.
    /// This is the operation that replaces `apply_local`: it allocates one
    /// environment cell per binder and copies nothing.
    pub fn apply(&mut self, c: &'v TmClo<'v>, args: &[&'v TmClo<'v>]) -> Res<Rc<Val<'v>>> {
        let w = match args {
            [a] => Work::Apply1(c, *a),
            _ => Work::Apply(c, args.to_vec()),
        };
        self.drive(w)
    }

    /// [`Eval::apply`] for type closures. A closure that is not syntactic has
    /// no pending binders and ignores them (`TyClo::Val` is a *constant*
    /// closure — the shape conversion's weakened annotations take).
    pub fn apply_ty(&mut self, c: &'v TyClo<'v>, args: &[&'v TmClo<'v>]) -> Res<Rc<VTy<'v>>> {
        if args.is_empty() {
            return self.force_ty(c);
        }
        match c {
            TyClo::Syn { env, body, .. } => {
                let (env, body) = (env.extend(self.arena, args), Rc::clone(body));
                self.eval_ty(&body, &env)
            }
            _ => self.force_ty(c),
        }
    }

    // -- δ ------------------------------------------------------------------

    /// Force exactly one glued definition at the head, leaving a newly
    /// exposed defined head glued. Conversion uses this to interleave
    /// unfolding with spine comparison: a transparent wrapper may reveal the
    /// same head as the other side without requiring either body to normalize
    /// completely.
    pub fn delta_step(&mut self, v: Rc<Val<'v>>) -> Res<Rc<Val<'v>>> {
        let unfold = match &*v {
            Val::Neutral(n) => n.unfold,
            _ => None,
        };
        match unfold {
            None => Ok(v),
            Some(u) => {
                self.spend()?;
                self.force(u)
            }
        }
    }

    /// Force the glued unfoldings at the head until the value is not a
    /// definition's spine — i.e. the δ-transparent weak head value.
    ///
    /// Conversion's δ-lazy stage deliberately does *not* call this until the
    /// opaque comparison has failed (design §5); it is the second stage, and
    /// the differential oracle's counterpart to `whnf_term_delta`.
    pub fn delta_whnf(&mut self, mut v: Rc<Val<'v>>) -> Res<Rc<Val<'v>>> {
        loop {
            let next = self.delta_step(Rc::clone(&v))?;
            if Rc::ptr_eq(&next, &v) {
                return Ok(v);
            }
            v = next;
        }
    }

    /// [`Eval::delta_step`] for types: advance exactly one definition in the
    /// term at which an `El`, `Vec`, or `Fin` is δ-stuck, then perform the
    /// newly enabled non-δ type computation.
    pub fn delta_step_ty(&mut self, v: Rc<VTy<'v>>) -> Res<Rc<VTy<'v>>> {
        enum Next<'v> {
            Done,
            El(Level, Rc<Val<'v>>),
            Vec(Level, &'v TyClo<'v>, Rc<Val<'v>>),
            Fin(Rc<Val<'v>>),
        }
        let next = match &*v {
            VTy::Neutral(VNeTy::El { level, tm }) => Next::El(level.clone(), Rc::clone(tm)),
            VTy::Vec { level, elem, len } => Next::Vec(level.clone(), *elem, Rc::clone(len)),
            VTy::Fin { len } => Next::Fin(Rc::clone(len)),
            _ => Next::Done,
        };
        match next {
            Next::Done => Ok(v),
            Next::El(level, tm) => {
                let d = self.delta_step(Rc::clone(&tm))?;
                if Rc::ptr_eq(&d, &tm) {
                    Ok(v)
                } else {
                    self.decode(&level, &d)
                }
            }
            Next::Vec(level, elem, len) => {
                let d = self.delta_step(Rc::clone(&len))?;
                if Rc::ptr_eq(&d, &len) {
                    Ok(v)
                } else {
                    self.vec_ty(&level, elem, &d)
                }
            }
            Next::Fin(len) => {
                let d = self.delta_step(Rc::clone(&len))?;
                if Rc::ptr_eq(&d, &len) {
                    Ok(v)
                } else {
                    self.fin_ty(&d)
                }
            }
        }
    }

    /// Force the glued unfoldings at a type's δ-stuck term until none
    /// remains.
    pub fn delta_whnf_ty(&mut self, mut v: Rc<VTy<'v>>) -> Res<Rc<VTy<'v>>> {
        loop {
            let next = self.delta_step_ty(Rc::clone(&v))?;
            if Rc::ptr_eq(&next, &v) {
                return Ok(v);
            }
            v = next;
        }
    }

    // -- types --------------------------------------------------------------

    /// Evaluate a type to a weak head normal type value.
    pub fn eval_ty(&mut self, t: &Type, env: &Env<'v>) -> Res<Rc<VTy<'v>>> {
        let yclo = |env: &Env<'v>, body: &Rc<Type>| {
            self.arena.ty(TyClo::new(*env, Rc::clone(body)))
        };
        let tclo = |env: &Env<'v>, body: &Rc<Term>| {
            self.arena.tm(TmClo::syn(*env, Rc::clone(body)))
        };
        let v = match t {
            Type::Nat => VTy::Nat,
            Type::Ty(l) => VTy::Ty(l.clone()),
            Type::Unit { level } => VTy::Unit { level: level.clone() },
            Type::Empty { level } => VTy::Empty { level: level.clone() },
            Type::SEmpty { level } => VTy::SEmpty { level: level.clone() },
            Type::Pi { dom_level, cod_level, dom, cod } => VTy::Pi {
                dom_level: dom_level.clone(),
                cod_level: cod_level.clone(),
                dom: yclo(env, dom),
                cod: yclo(env, cod),
            },
            Type::Sigma { fst_level, snd_level, fst, snd } => VTy::Sigma {
                fst_level: fst_level.clone(),
                snd_level: snd_level.clone(),
                fst: yclo(env, fst),
                snd: yclo(env, snd),
            },
            Type::W { shape_level, pos_level, shape, pos } => VTy::W {
                shape_level: shape_level.clone(),
                pos_level: pos_level.clone(),
                shape: yclo(env, shape),
                pos: yclo(env, pos),
            },
            Type::Wf { level, shape, arity } => VTy::Wf {
                level: level.clone(),
                shape: yclo(env, shape),
                arity: tclo(env, arity),
            },
            Type::Sum { lhs_level, rhs_level, lhs, rhs } => VTy::Sum {
                lhs_level: lhs_level.clone(),
                rhs_level: rhs_level.clone(),
                lhs: yclo(env, lhs),
                rhs: yclo(env, rhs),
            },
            Type::Id { level, ty, lhs, rhs } => VTy::Id {
                level: level.clone(),
                ty: yclo(env, ty),
                lhs: tclo(env, lhs),
                rhs: tclo(env, rhs),
            },
            Type::SEq { level, ty, lhs, rhs } => VTy::SEq {
                level: level.clone(),
                ty: yclo(env, ty),
                lhs: tclo(env, lhs),
                rhs: tclo(env, rhs),
            },
            Type::Squash { level, ty } => VTy::Squash {
                level: level.clone(),
                ty: yclo(env, ty),
            },
            Type::UPi { num_vars, level, body } => VTy::UPi {
                num_vars: *num_vars,
                level: level.clone(),
                body: yclo(env, body),
            },
            Type::CtxPi { level, body } => {
                VTy::CtxPi { level: level.clone(), body: yclo(env, body) }
            }
            Type::TyPi { ctx, arg_level, body_level, body } => VTy::TyPi {
                ctx: ctx.clone(),
                arg_level: arg_level.clone(),
                body_level: body_level.clone(),
                body: yclo(env, body),
            },
            Type::CodeTy { ctx, level } => {
                VTy::CodeTy { ctx: ctx.clone(), level: level.clone() }
            }
            Type::CodeTm { ctx, ty, level } => VTy::CodeTm {
                ctx: ctx.clone(),
                ty: Rc::clone(ty),
                level: level.clone(),
            },
            Type::GlobalTy { var, subst } => {
                let subst = self.eval_subst(subst, env)?;
                VTy::Neutral(VNeTy::Global { var: *var, subst })
            }
            // `El` is a redex-or-neutral and has no canonical value.
            Type::El { level, tm } => {
                let v = self.eval_tm(tm, env)?;
                return self.decode(level, &v);
            }
            // `Vec`/`Fin` step at a canonical length; the value exists only
            // over a stuck one.
            Type::Vec { level, elem, len } => {
                let lv = self.eval_tm(len, env)?;
                return self.vec_ty(level, yclo(env, elem), &lv);
            }
            Type::Fin { len } => {
                let lv = self.eval_tm(len, env)?;
                return self.fin_ty(&lv);
            }
        };
        Ok(Rc::new(v))
    }

    /// `El^l v` — decode an encoding *value*, or leave the neutral `El`.
    ///
    /// The decoded children are built as `El` **syntax** over the encoding
    /// child's own closure, so the decode stays one step deep: a `Π` is weak
    /// head normal and its domain is not reduced until someone asks.
    fn decode(&mut self, level: &Level, v: &Rc<Val<'v>>) -> Res<Rc<VTy<'v>>> {
        // `El^l c` as a lazy type. When `c` has syntax the `El` is built as
        // syntax over the child's own closure — one step deep, so a decoded
        // `Π`'s domain is not reduced until someone asks; otherwise the
        // domain's own lazy `El` says the same thing about a value.
        let arena = self.arena;
        let el = |l: &Level, c: &'v TmClo<'v>| -> Option<&'v TyClo<'v>> {
            Some(match c.as_syn() {
                Some((env, body)) => arena.ty(TyClo::new(
                    *env,
                    Rc::new(Type::El { level: l.clone(), tm: Rc::clone(body) }),
                )),
                None => arena.ty_el(l.clone(), c),
            })
        };
        let stuck_el =
            || Ok(Rc::new(VTy::Neutral(VNeTy::El { level: level.clone(), tm: Rc::clone(v) })));

        let decoded = match &**v {
            Val::TmNat => VTy::Nat,
            Val::TmTy(l) => VTy::Ty(l.clone()),
            Val::TmUnit { level } => VTy::Unit { level: level.clone() },
            Val::TmEmpty { level } => VTy::Empty { level: level.clone() },
            Val::TmSEmpty { level } => VTy::SEmpty { level: level.clone() },
            Val::TmSquash { level, ty } => {
                let Some(ty) = el(level, ty) else { return stuck_el() };
                VTy::Squash { level: level.clone(), ty }
            }
            Val::TmPi { dom_level, cod_level, dom, cod } => {
                let (Some(d), Some(c)) = (el(dom_level, dom), el(cod_level, cod)) else {
                    return stuck_el();
                };
                VTy::Pi {
                    dom_level: dom_level.clone(),
                    cod_level: cod_level.clone(),
                    dom: d,
                    cod: c,
                }
            }
            Val::TmSigma { fst_level, snd_level, fst, snd } => {
                let (Some(a), Some(b)) = (el(fst_level, fst), el(snd_level, snd)) else {
                    return stuck_el();
                };
                VTy::Sigma {
                    fst_level: fst_level.clone(),
                    snd_level: snd_level.clone(),
                    fst: a,
                    snd: b,
                }
            }
            Val::TmW { shape_level, pos_level, shape, pos } => {
                let (Some(s), Some(p)) = (el(shape_level, shape), el(pos_level, pos)) else {
                    return stuck_el();
                };
                VTy::W {
                    shape_level: shape_level.clone(),
                    pos_level: pos_level.clone(),
                    shape: s,
                    pos: p,
                }
            }
            Val::TmSum { lhs_level, rhs_level, lhs, rhs } => {
                let (Some(a), Some(b)) = (el(lhs_level, lhs), el(rhs_level, rhs)) else {
                    return stuck_el();
                };
                VTy::Sum {
                    lhs_level: lhs_level.clone(),
                    rhs_level: rhs_level.clone(),
                    lhs: a,
                    rhs: b,
                }
            }
            Val::TmId { level: l, ty, lhs, rhs } => {
                let Some(t) = el(l, ty) else { return stuck_el() };
                VTy::Id {
                    level: l.clone(),
                    ty: t,
                    lhs: *lhs,
                    rhs: *rhs,
                }
            }
            Val::TmSEq { level: l, ty, lhs, rhs } => {
                let Some(t) = el(l, ty) else { return stuck_el() };
                VTy::SEq {
                    level: l.clone(),
                    ty: t,
                    lhs: *lhs,
                    rhs: *rhs,
                }
            }
            // The arity rides across unchanged: it is a term under the same
            // binder, and only the shape decodes.
            Val::TmWf { level: l, shape, arity } => {
                let Some(s) = el(l, shape) else { return stuck_el() };
                VTy::Wf { level: l.clone(), shape: s, arity: *arity }
            }
            // `El (Vec s k) ⇝ Vec (El s) k`, which then steps at a canonical
            // length — so the decode continues into the `Vec` rule.
            Val::TmVec { level: l, elem, len } => {
                let Some(e) = el(l, elem) else { return stuck_el() };
                self.spend()?;
                let lv = self.force(len)?;
                let l = l.clone();
                return self.vec_ty(&l, e, &lv);
            }
            Val::TmFin { len } => {
                self.spend()?;
                let lv = self.force(len)?;
                return self.fin_ty(&lv);
            }
            _ => return stuck_el(),
        };
        self.spend()?;
        Ok(Rc::new(decoded))
    }

    /// `Vec^l(T; k)`: `0 ⇝ Unit^l`, `S k ⇝ Σ(_ : T). Vec^l(T; k)`, stuck
    /// otherwise.
    ///
    /// The Σ-tail is the **unforced** `Vec` of [`TyClo::Vec`], not syntax: the
    /// predecessor is a value with no syntax of its own, the element type need
    /// not have any either (conversion synthesizes `Vec`s over element types
    /// that are values), and evaluating the tail eagerly would unroll the
    /// whole tuple type at a literal length. Neither the tail nor the element
    /// mentions the Σ's own binder, and a non-syntactic closure ignores it.
    pub(crate) fn vec_ty(
        &mut self,
        level: &Level,
        elem: &'v TyClo<'v>,
        len: &Rc<Val<'v>>,
    ) -> Res<Rc<VTy<'v>>> {
        let out = match &**len {
            Val::Zero => {
                self.spend()?;
                VTy::Unit { level: level.clone() }
            }
            Val::Succ(pred) => {
                self.spend()?;
                VTy::Sigma {
                    fst_level: level.clone(),
                    snd_level: level.clone(),
                    fst: elem,
                    snd: self.arena.ty_vec(level.clone(), elem, pred),
                }
            }
            Val::NatRun { program, tail } => {
                self.spend()?;
                let pred = Val::nat_run_pred(self.arena, program, tail);
                VTy::Sigma {
                    fst_level: level.clone(),
                    snd_level: level.clone(),
                    fst: elem,
                    snd: self.arena.ty_vec(level.clone(), elem, pred),
                }
            }
            _ => VTy::Vec {
                level: level.clone(),
                elem,
                len: Rc::clone(len),
            },
        };
        Ok(Rc::new(out))
    }

    /// `Fin(k)`: `0 ⇝ Empty^0`, `S k ⇝ Unit^0 +^{0,0} Fin(k)`, stuck
    /// otherwise. Both reducts are closed apart from the predecessor, which
    /// again rides in the environment.
    fn fin_ty(&mut self, len: &Rc<Val<'v>>) -> Res<Rc<VTy<'v>>> {
        let out = match &**len {
            Val::Zero => {
                self.spend()?;
                VTy::Empty { level: Level::Zero }
            }
            Val::Succ(pred) => {
                self.spend()?;
                let rhs_env = Env::empty().push(self.arena, pred);
                VTy::Sum {
                    lhs_level: Level::Zero,
                    rhs_level: Level::Zero,
                    lhs: self.arena.ty(TyClo::new(
                        Env::empty(),
                        Rc::new(Type::Unit { level: Level::Zero }),
                    )),
                    rhs: self.arena.ty(TyClo::new(
                        rhs_env,
                        Rc::new(Type::Fin { len: Rc::new(Term::Var(LocalVar(0))) }),
                    )),
                }
            }
            Val::NatRun { program, tail } => {
                self.spend()?;
                let pred = Val::nat_run_pred(self.arena, program, tail);
                let rhs_env = Env::empty().push(self.arena, pred);
                VTy::Sum {
                    lhs_level: Level::Zero,
                    rhs_level: Level::Zero,
                    lhs: self.arena.ty(TyClo::new(
                        Env::empty(),
                        Rc::new(Type::Unit { level: Level::Zero }),
                    )),
                    rhs: self.arena.ty(TyClo::new(
                        rhs_env,
                        Rc::new(Type::Fin { len: Rc::new(Term::Var(LocalVar(0))) }),
                    )),
                }
            }
            _ => VTy::Fin { len: Rc::clone(len) },
        };
        Ok(Rc::new(out))
    }

    /// A local substitution inside a neutral: its terms become **values**,
    /// evaluated pointwise here. An unforced `δ` would be the defect class
    /// reintroduced by the domain (design §3.4).
    fn eval_subst(&mut self, d: &LocalSubst, env: &Env<'v>) -> Res<VSubst<'v>> {
        let mut terms = Vec::with_capacity(d.terms.len());
        for t in &d.terms {
            terms.push(self.eval_tm(t, env)?);
        }
        Ok(VSubst { tail: VTail::of(d.tail, self.base), terms })
    }

    // -- terms --------------------------------------------------------------

    /// Evaluate a term to a weak head normal value.
    pub fn eval_tm(&mut self, t: &Rc<Term>, env: &Env<'v>) -> Res<Rc<Val<'v>>> {
        self.eval_tm_ref(t, env)
    }

    /// [`Eval::eval_tm`] on a node the caller does not own — the **root** of a
    /// conversion, which is syntax lent to the checker. Wrapping it in an
    /// `Rc` just to start the machine cost 1.3× on `nat/check-numeral`, whose
    /// every conversion is one `Nat ≈ Nat`.
    pub fn eval_tm_ref(&mut self, t: &Term, env: &Env<'v>) -> Res<Rc<Val<'v>>> {
        let w = self.step_eval(t, env)?;
        self.drive(w)
    }

    /// One step of [`Eval::eval_tm`], with its **tail positions returned**
    /// rather than called: see [`Eval::drive`].
    fn step_eval(&mut self, t: &Term, env: &Env<'v>) -> Res<Work<'v>> {
        let yclo = |env: &Env<'v>, body: &Rc<Type>| {
            self.arena.ty(TyClo::new(*env, Rc::clone(body)))
        };
        let tclo = |env: &Env<'v>, body: &Rc<Term>| {
            self.arena.tm(TmClo::syn(*env, Rc::clone(body)))
        };
        let v = match t {
            Term::Var(x) => match env.lookup(x.0) {
                Lookup::Bound(c) => return Ok(Work::Force(c)),
                Lookup::Base(d) => Val::base_var(d),
            },

            // -- encodings --
            Term::TmNat => Val::TmNat,
            Term::TmTy(l) => Val::TmTy(l.clone()),
            Term::TmUnit { level } => Val::TmUnit { level: level.clone() },
            Term::TmEmpty { level } => Val::TmEmpty { level: level.clone() },
            Term::TmSEmpty { level } => Val::TmSEmpty { level: level.clone() },
            Term::TmSquash { level, ty } => Val::TmSquash {
                level: level.clone(),
                ty: tclo(env, ty),
            },
            Term::TmPi { dom_level, cod_level, dom, cod } => Val::TmPi {
                dom_level: dom_level.clone(),
                cod_level: cod_level.clone(),
                dom: tclo(env, dom),
                cod: tclo(env, cod),
            },
            Term::TmSigma { fst_level, snd_level, fst, snd } => Val::TmSigma {
                fst_level: fst_level.clone(),
                snd_level: snd_level.clone(),
                fst: tclo(env, fst),
                snd: tclo(env, snd),
            },
            Term::TmW { shape_level, pos_level, shape, pos } => Val::TmW {
                shape_level: shape_level.clone(),
                pos_level: pos_level.clone(),
                shape: tclo(env, shape),
                pos: tclo(env, pos),
            },
            Term::TmWf { level, shape, arity } => Val::TmWf {
                level: level.clone(),
                shape: tclo(env, shape),
                arity: tclo(env, arity),
            },
            Term::TmId { level, ty, lhs, rhs } => Val::TmId {
                level: level.clone(),
                ty: tclo(env, ty),
                lhs: tclo(env, lhs),
                rhs: tclo(env, rhs),
            },
            Term::TmSEq { level, ty, lhs, rhs } => Val::TmSEq {
                level: level.clone(),
                ty: tclo(env, ty),
                lhs: tclo(env, lhs),
                rhs: tclo(env, rhs),
            },
            Term::TmSum { lhs_level, rhs_level, lhs, rhs } => Val::TmSum {
                lhs_level: lhs_level.clone(),
                rhs_level: rhs_level.clone(),
                lhs: tclo(env, lhs),
                rhs: tclo(env, rhs),
            },
            Term::TmVec { level, elem, len } => Val::TmVec {
                level: level.clone(),
                elem: tclo(env, elem),
                len: tclo(env, len),
            },
            Term::TmFin { len } => Val::TmFin { len: tclo(env, len) },

            // -- data --
            Term::Zero => Val::Zero,
            Term::NatLit(0) => Val::Zero,
            Term::NatLit(n) => Val::NatRun {
                program: ContextProgram::run(
                    (),
                    NonZeroU64::new(*n).expect("nonzero NatLit arm"),
                ),
                tail: self.arena.tm(TmClo::val(Rc::new(Val::Zero))),
            },
            Term::Succ(p) => Val::Succ(tclo(env, p)),
            Term::Refl { level, ty, tm } => Val::Refl {
                level: level.clone(),
                ty: yclo(env, ty),
                tm: tclo(env, tm),
            },
            Term::SRefl { level, ty, tm } => Val::SRefl {
                level: level.clone(),
                ty: yclo(env, ty),
                tm: tclo(env, tm),
            },
            Term::Squash { level, ty, tm } => Val::Squash {
                level: level.clone(),
                ty: yclo(env, ty),
                tm: tclo(env, tm),
            },
            Term::Pair { fst_level, snd_level, fst_ty, snd_ty, fst, snd } => Val::Pair {
                fst_level: fst_level.clone(),
                snd_level: snd_level.clone(),
                fst_ty: yclo(env, fst_ty),
                snd_ty: yclo(env, snd_ty),
                fst: tclo(env, fst),
                snd: tclo(env, snd),
            },
            Term::Triv { level } => Val::Triv { level: level.clone() },
            Term::Inl { lhs_level, rhs_level, lhs, rhs, val } => Val::Inl {
                lhs_level: lhs_level.clone(),
                rhs_level: rhs_level.clone(),
                lhs: yclo(env, lhs),
                rhs: yclo(env, rhs),
                val: tclo(env, val),
            },
            Term::Inr { lhs_level, rhs_level, lhs, rhs, val } => Val::Inr {
                lhs_level: lhs_level.clone(),
                rhs_level: rhs_level.clone(),
                lhs: yclo(env, lhs),
                rhs: yclo(env, rhs),
                val: tclo(env, val),
            },
            Term::Sup { shape_level, pos_level, shape_ty, pos_ty, label, children } => {
                Val::Sup {
                    shape_level: shape_level.clone(),
                    pos_level: pos_level.clone(),
                    shape_ty: yclo(env, shape_ty),
                    pos_ty: yclo(env, pos_ty),
                    label: tclo(env, label),
                    children: tclo(env, children),
                }
            }
            Term::Supf { level, shape, arity, label, children } => Val::Supf {
                level: level.clone(),
                shape: yclo(env, shape),
                arity: tclo(env, arity),
                label: tclo(env, label),
                children: tclo(env, children),
            },

            // -- functions --
            Term::Lam { dom_level, cod_level, dom, body } => Val::Lam {
                dom_level: dom_level.clone(),
                cod_level: cod_level.clone(),
                dom: yclo(env, dom),
                body: tclo(env, body),
            },
            Term::ULam { num_vars, level, body } => Val::ULam {
                num_vars: *num_vars,
                level: level.clone(),
                body: tclo(env, body),
            },
            Term::CtxLam { level, body } => {
                Val::CtxLam { level: level.clone(), body: tclo(env, body) }
            }
            Term::TyLam { ctx, arg_level, body_level, body } => Val::TyLam {
                ctx: ctx.clone(),
                arg_level: arg_level.clone(),
                body_level: body_level.clone(),
                body: tclo(env, body),
            },

            // -- code: inert, and carrying no environment --
            Term::BoxTy(c) => Val::BoxTy(Rc::clone(c)),
            Term::BoxTm(c) => Val::BoxTm(Rc::clone(c)),

            // -- globals: glued neutrals --
            Term::GlobalTm { var, subst } => {
                let subst = self.eval_subst(subst, env)?;
                return Ok(Work::Val(self.global_tm(*var, subst)));
            }

            // -- eliminations --
            Term::App { fun, dom_level, cod_level, dom, cod, arg } => {
                let f = self.eval_tm(fun, env)?;
                let e = Elim::App {
                    dom_level: dom_level.clone(),
                    cod_level: cod_level.clone(),
                    dom: yclo(env, dom),
                    cod: yclo(env, cod),
                    arg: tclo(env, arg),
                };
                return Ok(Work::Elim(f, e));
            }
            Term::UApp { fun, levels } => {
                let f = self.eval_tm(fun, env)?;
                return Ok(Work::Elim(f, Elim::UApp { levels: levels.clone() }));
            }
            Term::CtxApp { fun, ctx } => {
                let f = self.eval_tm(fun, env)?;
                return Ok(Work::Elim(f, Elim::CtxApp { ctx: ctx.clone() }));
            }
            Term::TyApp { fun, arg } => {
                let f = self.eval_tm(fun, env)?;
                return Ok(Work::Elim(f, Elim::TyApp { arg: Rc::clone(arg) }));
            }
            Term::Fst { fst_level, snd_level, fst_ty, snd_ty, pair } => {
                let p = self.eval_tm(pair, env)?;
                let e = Elim::Fst {
                    fst_level: fst_level.clone(),
                    snd_level: snd_level.clone(),
                    fst_ty: yclo(env, fst_ty),
                    snd_ty: yclo(env, snd_ty),
                };
                return Ok(Work::Elim(p, e));
            }
            Term::Snd { fst_level, snd_level, fst_ty, snd_ty, pair } => {
                let p = self.eval_tm(pair, env)?;
                let e = Elim::Snd {
                    fst_level: fst_level.clone(),
                    snd_level: snd_level.clone(),
                    fst_ty: yclo(env, fst_ty),
                    snd_ty: yclo(env, snd_ty),
                };
                return Ok(Work::Elim(p, e));
            }
            Term::ElimNat { level, motive, base, step, scrut } => {
                let s = self.eval_tm(scrut, env)?;
                let e = Elim::ElimNat {
                    level: level.clone(),
                    motive: yclo(env, motive),
                    base: tclo(env, base),
                    step: tclo(env, step),
                };
                return Ok(Work::Elim(s, e));
            }
            Term::ElimEmpty { level, scrut_level, motive, scrut } => {
                let s = self.eval_tm(scrut, env)?;
                let e = Elim::ElimEmpty {
                    level: level.clone(),
                    scrut_level: scrut_level.clone(),
                    motive: yclo(env, motive),
                };
                return Ok(Work::Elim(s, e));
            }
            Term::ElimSEmpty { level, scrut_level, motive, scrut } => {
                let s = self.eval_tm(scrut, env)?;
                let e = Elim::ElimSEmpty {
                    level: level.clone(),
                    scrut_level: scrut_level.clone(),
                    motive: yclo(env, motive),
                };
                return Ok(Work::Elim(s, e));
            }
            Term::ElimSquash { src_level, dst_level, src_ty, motive, case, scrut } => {
                let s = self.eval_tm(scrut, env)?;
                let e = Elim::ElimSquash {
                    src_level: src_level.clone(),
                    dst_level: dst_level.clone(),
                    src_ty: yclo(env, src_ty),
                    motive: yclo(env, motive),
                    case: tclo(env, case),
                };
                return Ok(Work::Elim(s, e));
            }
            Term::Case {
                lhs_level,
                rhs_level,
                motive_level,
                lhs,
                rhs,
                motive,
                case_l,
                case_r,
                scrut,
            } => {
                let s = self.eval_tm(scrut, env)?;
                let e = Elim::Case {
                    lhs_level: lhs_level.clone(),
                    rhs_level: rhs_level.clone(),
                    motive_level: motive_level.clone(),
                    lhs: yclo(env, lhs),
                    rhs: yclo(env, rhs),
                    motive: yclo(env, motive),
                    case_l: tclo(env, case_l),
                    case_r: tclo(env, case_r),
                };
                return Ok(Work::Elim(s, e));
            }
            Term::ElimW {
                shape_level,
                pos_level,
                motive_level,
                shape,
                pos,
                motive,
                step,
                scrut,
            } => {
                let s = self.eval_tm(scrut, env)?;
                let e = Elim::ElimW {
                    shape_level: shape_level.clone(),
                    pos_level: pos_level.clone(),
                    motive_level: motive_level.clone(),
                    shape: yclo(env, shape),
                    pos: yclo(env, pos),
                    motive: yclo(env, motive),
                    step: tclo(env, step),
                    env: env.clone(),
                };
                return Ok(Work::Elim(s, e));
            }
            Term::ElimWf { level, motive_level, shape, arity, motive, step, scrut } => {
                let s = self.eval_tm(scrut, env)?;
                let e = Elim::ElimWf {
                    level: level.clone(),
                    motive_level: motive_level.clone(),
                    shape: yclo(env, shape),
                    arity: tclo(env, arity),
                    motive: yclo(env, motive),
                    step: tclo(env, step),
                    env: env.clone(),
                };
                return Ok(Work::Elim(s, e));
            }
            Term::J { ty_level, motive_level, ty, lhs, motive, case, rhs, proof } => {
                let p = self.eval_tm(proof, env)?;
                let e = Elim::J {
                    ty_level: ty_level.clone(),
                    motive_level: motive_level.clone(),
                    ty: yclo(env, ty),
                    lhs: tclo(env, lhs),
                    motive: yclo(env, motive),
                    case: tclo(env, case),
                    rhs: tclo(env, rhs),
                };
                return Ok(Work::Elim(p, e));
            }
            Term::Transp { ty_level, motive_level, ty, motive, lhs, rhs, proof, tm } => {
                let p = self.eval_tm(proof, env)?;
                let e = Elim::Transp {
                    ty_level: ty_level.clone(),
                    motive_level: motive_level.clone(),
                    ty: yclo(env, ty),
                    motive: yclo(env, motive),
                    lhs: tclo(env, lhs),
                    rhs: tclo(env, rhs),
                    tm: tclo(env, tm),
                };
                return Ok(Work::Elim(p, e));
            }
            Term::LetBoxTy { motive_level, code_level, ctx, motive, body, scrut } => {
                let s = self.eval_tm(scrut, env)?;
                let e = Elim::LetBoxTy {
                    motive_level: motive_level.clone(),
                    code_level: code_level.clone(),
                    ctx: ctx.clone(),
                    motive: yclo(env, motive),
                    body: tclo(env, body),
                };
                return Ok(Work::Elim(s, e));
            }
            Term::LetBoxTm { motive_level, code_level, ctx, ty, motive, body, scrut } => {
                let s = self.eval_tm(scrut, env)?;
                let e = Elim::LetBoxTm {
                    motive_level: motive_level.clone(),
                    code_level: code_level.clone(),
                    ctx: ctx.clone(),
                    ty: Rc::clone(ty),
                    motive: yclo(env, motive),
                    body: tclo(env, body),
                };
                return Ok(Work::Elim(s, e));
            }
            Term::ElimCodeTy {
                ty_motive_level,
                tm_motive_level,
                motives,
                branches,
                code_level,
                ctx,
                scrut,
            } => {
                let s = self.eval_tm(scrut, env)?;
                let e = Elim::ElimCodeTy {
                    ty_motive_level: ty_motive_level.clone(),
                    tm_motive_level: tm_motive_level.clone(),
                    motives: Rc::clone(motives),
                    branches: Rc::clone(branches),
                    code_level: code_level.clone(),
                    ctx: ctx.clone(),
                    env: env.clone(),
                };
                return Ok(Work::Elim(s, e));
            }
            Term::ElimCodeTm {
                ty_motive_level,
                tm_motive_level,
                motives,
                branches,
                code_level,
                ctx,
                ty,
                scrut,
            } => {
                // Fixed order (ch. 06): the type annotation — scoped in Δ,
                // not Γ — reaches WHNF before the scrutinee is touched. It
                // stays syntax, so it is the rewriter that reduces it.
                let wty = self.whnf_ty_syntax(ty, ctx)?;
                let s = self.eval_tm(scrut, env)?;
                let e = Elim::ElimCodeTm {
                    ty_motive_level: ty_motive_level.clone(),
                    tm_motive_level: tm_motive_level.clone(),
                    motives: Rc::clone(motives),
                    branches: Rc::clone(branches),
                    code_level: code_level.clone(),
                    ctx: ctx.clone(),
                    ty: wty,
                    env: env.clone(),
                };
                return Ok(Work::Elim(s, e));
            }
        };
        Ok(Work::Val(Rc::new(v)))
    }

    /// `u^δ` as a glued neutral: `unfold` is `Some` exactly when `Defs` says
    /// `u` is a definition here, and it evaluates the (already rescoped) body
    /// under δ's **value** environment.
    ///
    /// That environment is δ's payload values alone: `wk^k_g` maps the
    /// abstract prefix of Δ to the abstract prefix of Γ identically, and
    /// `·^k_{g?}` targets an empty Δ, so past the payloads the lookup falls
    /// through to the same [`Head::BaseVar`] numbering either way.
    fn global_tm(&mut self, var: GlobalVar, subst: VSubst<'v>) -> Rc<Val<'v>> {
        let unfold = self.defs.body(var).map(|body| {
            let mut denv = Env::empty();
            for v in &subst.terms {
                denv = denv.push(self.arena, self.vclo(Rc::clone(v)));
            }
            self.arena.tm(TmClo::syn(denv, body))
        });
        neutral(Head::Global { var, subst }, ElimSpine::empty(), unfold)
    }

    /// `T ⇝* W` on **syntax**, in a local context that is not the ambient
    /// one. The single customer is `elim^Trm`'s type annotation (scoped in
    /// Δ); it is off the hot path and the design keeps Δ syntactic (§3.4).
    fn whnf_ty_syntax(&mut self, t: &Rc<Type>, gamma: &LocalCtx) -> Res<Rc<Type>> {
        let mut cur = Rc::clone(t);
        while let Some(next) = step_type_delta(&cur, gamma, self.defs) {
            self.spend()?;
            cur = Rc::new(next);
        }
        Ok(cur)
    }

    // -- elimination --------------------------------------------------------

    /// Apply one elimination to a weak head value: fire its β, or extend the
    /// neutral's spine (and, when the neutral is glued, its unfolding).
    pub fn elim(&mut self, head: Rc<Val<'v>>, e: Elim<'v>) -> Res<Rc<Val<'v>>> {
        self.drive(Work::Elim(head, e))
    }

    /// One step of [`Eval::elim`]; see [`Eval::drive`].
    fn step_elim(&mut self, head: Rc<Val<'v>>, e: Elim<'v>) -> Res<Work<'v>> {
        if let Val::Neutral(n) = &*head {
            // A Nat fold the run machinery accelerates — the successor
            // algebra or the synchronous two-counter fold — whose scrutinee
            // is a *glued* definition unfolds that scrutinee here rather
            // than stalling as a spine for conversion to δ-step from the
            // outside one definition at a time (each such step replays the
            // whole pending spine, so a chain of `p + p` doublings under a
            // literal consumer was cubic in the chain). Only these folds do
            // so: their scrutinee is closed arithmetic whenever the fold
            // can fire at all, and an open one stops at its variable. A
            // general match or recursor must NOT: the x86 decoder's
            // open-argument unfolding theorems meet at a *folded* scrutinee
            // (`match decode_opcode_direct(…)` on both sides), and unfolding
            // it eagerly exhausts fuel on the dispatch it hides.
            if let (Some(unfold), Elim::ElimNat { step, .. }) = (n.unfold, &e) {
                if nat_step_successors(step).is_some() || nat_step_synchronizes(step) {
                    self.spend()?;
                    self.frames.push(Frame::Elim(Rc::new(e)));
                    return Ok(Work::Force(unfold));
                }
            }
            let n = Rc::clone(n);
            return Ok(Work::Val(self.push_elim(&n, e)));
        }
        match (&*head, &e) {
            (
                Val::NatSync { program, tail, elim },
                Elim::App { dom_level, cod_level, dom, cod, arg },
            ) => {
                let right = self.force(arg)?;
                if let Val::Neutral(rn) = &*right {
                    if let Some(unfold) = rn.unfold {
                        // The counter on the right is a glued definition
                        // (`sub(x, p)` feeding the next comparison): unfold
                        // it and retry, for the reason given at the neutral
                        // scrutinee case above.
                        self.spend()?;
                        self.frames.push(Frame::SyncArg {
                            head: Rc::clone(&head),
                            app: Rc::new(e.clone()),
                        });
                        return Ok(Work::Force(unfold));
                    }
                }
                if let Val::NatRun { program: right_program, tail: right_tail } = &*right {
                    let cancelled = ContextProgram::cancel_matching_prefix(
                        Rc::clone(program),
                        Rc::clone(right_program),
                        self.fuel.saturating_sub(1),
                    )
                    .map_err(|_| {
                        self.fuel = 0;
                        OutOfFuel
                    })?;
                    self.fuel -= cancelled.inspected;
                    if cancelled.changed {
                        self.spend()?;
                        let left = self.nat_residual(cancelled.left, tail);
                        let right = self.nat_residual(cancelled.right, right_tail);
                        let folded = self.arena.tm(TmClo::elim(left, Rc::clone(elim)));
                        let app = Elim::App {
                            dom_level: dom_level.clone(),
                            cod_level: cod_level.clone(),
                            dom,
                            cod,
                            arg: right,
                        };
                        self.frames.push(Frame::Elim(Rc::new(app)));
                        return Ok(Work::Force(folded));
                    }
                }

                // The right-hand head is not a matching run. Expose exactly
                // the ordinary outer successor step and retry the application
                // on its result; no semantic case is guessed here.
                let pred = Val::nat_run_pred(self.arena, program, tail);
                let ih = self.arena.tm(TmClo::elim(pred, Rc::clone(elim)));
                let Elim::ElimNat { step, .. } = &**elim else {
                    unreachable!("NatSync stores a Nat eliminator")
                };
                self.frames.push(Frame::Elim(Rc::new(e)));
                self.spend()?;
                Ok(Work::Apply(*step, vec![pred, ih]))
            }
            (Val::Lam { body, .. }, Elim::App { arg, .. }) => {
                self.spend()?;
                let (body, arg) = (*body, *arg);
                Ok(Work::Apply1(body, arg))
            }
            (Val::ULam { num_vars, body, .. }, Elim::UApp { levels })
                if *num_vars as usize == levels.len() =>
            {
                self.spend()?;
                let Some((benv, bbody)) = body.as_syn() else { return Ok(Work::Val(stuck(self.arena, &head, &e))) };
                // The written vectors pair positionally (outermost first);
                // instantiation wants innermost-first.
                let phi: Vec<Level> = levels.iter().rev().cloned().collect();
                let (benv, inst) = (benv.clone(), Rc::new(bbody.inst_univ(&phi)));
                Ok(Work::Eval(inst, benv))
            }
            (Val::CtxLam { body, .. }, Elim::CtxApp { ctx }) => {
                self.spend()?;
                let Some((benv, bbody)) = body.as_syn() else { return Ok(Work::Val(stuck(self.arena, &head, &e))) };
                let sigma = GlobalSubst::single(GlobalEntry::Ctx(ctx.clone()));
                let (benv, inst) = (benv.clone(), Rc::new(bbody.apply_global(&sigma)));
                Ok(Work::Eval(inst, benv))
            }
            (Val::TyLam { body, .. }, Elim::TyApp { arg }) => {
                self.spend()?;
                let Some((benv, bbody)) = body.as_syn() else { return Ok(Work::Val(stuck(self.arena, &head, &e))) };
                let sigma = GlobalSubst::single(GlobalEntry::Ty(Rc::clone(arg)));
                let (benv, inst) = (benv.clone(), Rc::new(bbody.apply_global(&sigma)));
                Ok(Work::Eval(inst, benv))
            }
            (Val::Zero, Elim::ElimNat { base, .. }) => {
                self.spend()?;
                let base = *base;
                Ok(Work::Force(base))
            }
            // `elim_Nat … (su t) ⇝ s'[t/x, elim_Nat … t/y]`: the induction
            // hypothesis is a *pending* elimination, so a step that ignores
            // it costs nothing.
            (Val::Succ(pred), Elim::ElimNat { step, .. }) => {
                self.spend()?;
                let (pred, step) = (*pred, *step);
                let ih = self.arena.tm(TmClo::elim(pred, Rc::new(e.clone())));
                Ok(Work::Apply(step, vec![pred, ih]))
            }
            (Val::NatRun { program, tail }, Elim::ElimNat { step, .. }) => {
                self.spend()?;
                if nat_step_synchronizes(step) {
                    return Ok(Work::Val(Rc::new(Val::NatSync {
                        program: Rc::clone(program),
                        tail,
                        elim: Rc::new(e.clone()),
                    })));
                }
                if let Some(mapped) = nat_step_successors(step).and_then(|p| {
                    if p == 1 {
                        return Some(Rc::clone(program));
                    }
                    // A wider algebra scales one saturated run's count; a
                    // composed program, or a count that would overflow,
                    // takes the ordinary one-step path below.
                    let ContextProgram::Run { context, count } = &**program else { return None };
                    let scaled = count.get().checked_mul(p)?;
                    Some(ContextProgram::run(*context, NonZeroU64::new(scaled).unwrap()))
                }) {
                    // The fold at the tail is forced now rather than left
                    // pending, so that a run it produces merges with this
                    // one (`Frame::NatRunTail`). The value is the same
                    // either way; only its fragment count differs.
                    let mapped_tail = self.arena.tm(TmClo::elim(tail, Rc::new(e.clone())));
                    self.frames.push(Frame::NatRunTail { program: mapped, glued: None });
                    return Ok(Work::Force(mapped_tail));
                }
                let pred = Val::nat_run_pred(self.arena, program, tail);
                let ih = self.arena.tm(TmClo::elim(pred, Rc::new(e.clone())));
                Ok(Work::Apply(*step, vec![pred, ih]))
            }
            (Val::Refl { .. }, Elim::J { case, .. }) => {
                self.spend()?;
                let case = *case;
                Ok(Work::Force(case))
            }
            (Val::SRefl { .. }, Elim::Transp { tm, .. }) => {
                self.spend()?;
                let tm = *tm;
                Ok(Work::Force(tm))
            }
            (Val::Squash { tm, .. }, Elim::ElimSquash { case, .. }) => {
                self.spend()?;
                Ok(Work::Apply1(*case, *tm))
            }
            (Val::Pair { fst, .. }, Elim::Fst { .. }) => {
                self.spend()?;
                let fst = *fst;
                Ok(Work::Force(fst))
            }
            (Val::Pair { snd, .. }, Elim::Snd { .. }) => {
                self.spend()?;
                let snd = *snd;
                Ok(Work::Force(snd))
            }
            (Val::Inl { val, .. }, Elim::Case { case_l, .. }) => {
                self.spend()?;
                let (val, case_l) = (*val, *case_l);
                Ok(Work::Apply1(case_l, val))
            }
            (Val::Inr { val, .. }, Elim::Case { case_r, .. }) => {
                self.spend()?;
                let (val, case_r) = (*val, *case_r);
                Ok(Work::Apply1(case_r, val))
            }
            (Val::Sup { label, children, .. }, Elim::ElimW { .. }) => {
                self.spend()?;
                let (label, children) = (*label, *children);
                match self.fire_elim_w(label, children, &e)? {
                    Some(v) => Ok(v),
                    None => Ok(Work::Val(stuck(self.arena, &head, &e))),
                }
            }
            (Val::Supf { label, children, .. }, Elim::ElimWf { .. }) => {
                self.spend()?;
                let (label, children) = (*label, *children);
                match self.fire_elim_wf(label, children, &e)? {
                    Some(v) => Ok(v),
                    None => Ok(Work::Val(stuck(self.arena, &head, &e))),
                }
            }
            (Val::BoxTy(code), Elim::LetBoxTy { body, .. }) => {
                self.spend()?;
                let Some((benv, bbody)) = body.as_syn() else { return Ok(Work::Val(stuck(self.arena, &head, &e))) };
                let sigma = GlobalSubst::single(GlobalEntry::Ty(Rc::clone(code)));
                let (benv, inst) = (benv.clone(), Rc::new(bbody.apply_global(&sigma)));
                Ok(Work::Eval(inst, benv))
            }
            (Val::BoxTm(code), Elim::LetBoxTm { body, .. }) => {
                self.spend()?;
                let Some((benv, bbody)) = body.as_syn() else { return Ok(Work::Val(stuck(self.arena, &head, &e))) };
                let sigma = GlobalSubst::single(GlobalEntry::Tm(Rc::clone(code)));
                let (benv, inst) = (benv.clone(), Rc::new(bbody.apply_global(&sigma)));
                Ok(Work::Eval(inst, benv))
            }
            // `box (U^δ)` blocks the recursor: canonical, but neutral as a
            // whole (ch. 06), which is why the box becomes the head.
            (Val::BoxTy(code), Elim::ElimCodeTy { .. }) => {
                if matches!(&**code, Type::GlobalTy { .. }) {
                    return Ok(Work::Val(neutral(
                        Head::BoxedGlobalTy(Rc::clone(code)),
                        self.arena.elim(ElimSpine::empty(), e.clone()),
                        None,
                    )));
                }
                let code = Rc::clone(code);
                match self.fire_code_ty(&code, &e)? {
                    Some(v) => Ok(v),
                    None => Ok(Work::Val(stuck(self.arena, &head, &e))),
                }
            }
            (Val::BoxTm(code), Elim::ElimCodeTm { .. }) => {
                if matches!(&**code, Term::GlobalTm { .. }) {
                    return Ok(Work::Val(neutral(
                        Head::BoxedGlobalTm(Rc::clone(code)),
                        self.arena.elim(ElimSpine::empty(), e.clone()),
                        None,
                    )));
                }
                let code = Rc::clone(code);
                match self.fire_code_tm(&code, &e)? {
                    Some(v) => Ok(v),
                    None => Ok(Work::Val(stuck(self.arena, &head, &e))),
                }
            }
            _ => Ok(Work::Val(stuck(self.arena, &head, &e))),
        }
    }

    /// Extend a neutral's spine — and, when it is glued, its pending
    /// unfolding by the same elimination, so that forcing the unfolding
    /// replays the spine (design §5).
    fn push_elim(&mut self, n: &Rc<VNeutral<'v>>, e: Elim<'v>) -> Rc<Val<'v>> {
        let unfold = n
            .unfold
            .as_ref()
            .map(|u| self.arena.tm(TmClo::elim(u, Rc::new(e.clone()))));
        let spine = self.arena.elim(n.spine, e);
        neutral(n.head.clone(), spine, unfold)
    }

    /// `elim_W (sup(…; a; f)) ⇝ s[a/a, f/f, (λ y. elim_W …(f y))/ih]`.
    ///
    /// The ih is the one β that synthesizes a λ. Rather than a native
    /// closure, it is built as an ordinary syntactic closure over the
    /// environment `ρ, a, f`: the recursive eliminator is *exactly*
    /// `reduce.rs`'s term with `a` and `f` named by de Bruijn slots instead
    /// of substituted, which is why its adequacy is by inspection. The
    /// whole-node `shift_local(3)` is `reduce.rs`'s `shift_local(1)` widened
    /// by the two extra slots, and it descends the annotations' own binders
    /// for the same reason.
    fn fire_elim_w(
        &mut self,
        label: &'v TmClo<'v>,
        children: &'v TmClo<'v>,
        e: &Elim<'v>,
    ) -> Res<Option<Work<'v>>> {
        let Elim::ElimW {
            shape_level,
            pos_level,
            motive_level,
            shape,
            pos,
            motive,
            step,
            env,
        } = e
        else {
            return Ok(None);
        };
        let Some((_, step_body)) = step.as_syn() else { return Ok(None) };
        let (Some((_, shape_body)), Some((_, pos_body)), Some((_, motive_body))) =
            (shape.as_syn(), pos.as_syn(), motive.as_syn())
        else {
            return Ok(None);
        };
        let rho_af = env.push(self.arena, label).push(self.arena, children);
        let lmax = Level::max(shape_level.clone(), pos_level.clone());
        let w_syn = Type::W {
            shape_level: shape_level.clone(),
            pos_level: pos_level.clone(),
            shape: Rc::clone(shape_body),
            pos: Rc::clone(pos_body),
        };
        let template = Term::ElimW {
            shape_level: shape_level.clone(),
            pos_level: pos_level.clone(),
            motive_level: motive_level.clone(),
            shape: Rc::clone(shape_body),
            pos: Rc::clone(pos_body),
            motive: Rc::clone(motive_body),
            step: Rc::clone(step_body),
            scrut: Rc::new(Term::Zero),
        }
        .shift_local(3);
        let Term::ElimW { shape: s3, pos: p3, motive: m3, step: st3, .. } = template else {
            unreachable!("shifting an elim_W yields an elim_W")
        };
        // `f y` in `(Γ, a, f, y)`: `f` is slot 1, `y` slot 0, and the App's
        // codomain annotation binds one more.
        let f_y = Term::App {
            fun: Rc::new(Term::Var(LocalVar(1))),
            dom_level: pos_level.clone(),
            cod_level: lmax.clone(),
            dom: Rc::new(pos_body.shift_local(2)),
            cod: Rc::new(w_syn.shift_local(4)),
            arg: Rc::new(Term::Var(LocalVar(0))),
        };
        let rec = Term::ElimW {
            shape_level: shape_level.clone(),
            pos_level: pos_level.clone(),
            motive_level: motive_level.clone(),
            shape: s3,
            pos: p3,
            motive: m3,
            step: st3,
            scrut: Rc::new(f_y),
        };
        let ih = Rc::new(Val::Lam {
            dom_level: pos_level.clone(),
            cod_level: motive_level.clone(),
            // `T[a/x]` in `(Γ, a, f)`: `a` is slot 1.
            dom: self.arena.ty(TyClo::new(rho_af, Rc::new(pos_body.shift_local(1)))),
            body: self.arena.tm(TmClo::syn(rho_af, Rc::new(rec))),
        });
        let step = *step;
        Ok(Some(Work::Apply(
            step,
            vec![label, children, self.vclo(ih)],
        )))
    }

    /// `elim_Wf (sup_f(…; a; cs)) ⇝ s[a, cs, λ i. elim_Wf(…; nth … cs i)]`.
    /// [`fire_elim_w`](Eval::fire_elim_w)'s construction, with the child
    /// reached through the shared [`nth`] schema instead of an application.
    fn fire_elim_wf(
        &mut self,
        label: &'v TmClo<'v>,
        children: &'v TmClo<'v>,
        e: &Elim<'v>,
    ) -> Res<Option<Work<'v>>> {
        let Elim::ElimWf { level, motive_level, shape, arity, motive, step, env } = e else {
            return Ok(None);
        };
        let Some((_, step_body)) = step.as_syn() else { return Ok(None) };
        let Some((_, arity_body)) = arity.as_syn() else { return Ok(None) };
        let (Some((_, shape_body)), Some((_, motive_body))) = (shape.as_syn(), motive.as_syn())
        else {
            return Ok(None);
        };
        let rho_acs = env.push(self.arena, label).push(self.arena, children);
        let wf_syn = Type::Wf {
            level: level.clone(),
            shape: Rc::clone(shape_body),
            arity: Rc::clone(arity_body),
        };
        let template = Term::ElimWf {
            level: level.clone(),
            motive_level: motive_level.clone(),
            shape: Rc::clone(shape_body),
            arity: Rc::clone(arity_body),
            motive: Rc::clone(motive_body),
            step: Rc::clone(step_body),
            scrut: Rc::new(Term::Zero),
        }
        .shift_local(3);
        let Term::ElimWf { shape: s3, arity: n3, motive: m3, step: st3, .. } = template else {
            unreachable!("shifting an elim_Wf yields an elim_Wf")
        };
        // `nth(Wf; n[a/x]; cs; i)` in `(Γ, a, cs, i)`: `a` is slot 2, so the
        // arity's own binder lands on it under a shift of 2.
        let child = nth(
            level,
            &Rc::new(wf_syn.shift_local(3)),
            &Rc::new(arity_body.shift_local(2)),
            Rc::new(Term::Var(LocalVar(1))),
            Rc::new(Term::Var(LocalVar(0))),
        );
        let rec = Term::ElimWf {
            level: level.clone(),
            motive_level: motive_level.clone(),
            shape: s3,
            arity: n3,
            motive: m3,
            step: st3,
            scrut: Rc::new(child),
        };
        let ih = Rc::new(Val::Lam {
            dom_level: Level::Zero,
            cod_level: motive_level.clone(),
            dom: self.arena.ty(TyClo::new(
                rho_acs,
                Rc::new(Type::Fin { len: Rc::new(arity_body.shift_local(1)) }),
            )),
            body: self.arena.tm(TmClo::syn(rho_acs, Rc::new(rec))),
        });
        let step = *step;
        Ok(Some(Work::Apply(
            step,
            vec![label, children, self.vclo(ih)],
        )))
    }

    /// `elim^Typ … (box code)`: the fired branch comes from the *shared*
    /// [`beta_elim_ty`] as syntax in the current Γ, and is then evaluated in
    /// the current environment. `None` is `reduce.rs`'s own stuck case (a
    /// layer-m type that cannot be code).
    fn fire_code_ty(&mut self, code: &Rc<Type>, e: &Elim<'v>) -> Res<Option<Work<'v>>> {
        let Elim::ElimCodeTy {
            ty_motive_level,
            tm_motive_level,
            motives,
            branches,
            ctx,
            env,
            ..
        } = e
        else {
            return Ok(None);
        };
        let rec = Rec::new(ty_motive_level, tm_motive_level, motives, branches);
        let gamma = self.scope(env);
        let Some(fired) = beta_elim_ty(&rec, ctx, code, &gamma) else {
            return Ok(None);
        };
        self.spend()?;
        Ok(Some(Work::Eval(Rc::new(fired), env.clone())))
    }

    /// [`fire_code_ty`](Eval::fire_code_ty) for `elim^Trm`; the type
    /// annotation in the elimination is already in WHNF, as its β requires.
    fn fire_code_tm(&mut self, code: &Rc<Term>, e: &Elim<'v>) -> Res<Option<Work<'v>>> {
        let Elim::ElimCodeTm {
            ty_motive_level,
            tm_motive_level,
            motives,
            branches,
            code_level,
            ctx,
            ty,
            env,
        } = e
        else {
            return Ok(None);
        };
        let rec = Rec::new(ty_motive_level, tm_motive_level, motives, branches);
        let gamma = self.scope(env);
        let Some(fired) = beta_elim_tm(&rec, ctx, ty, code_level, code, &gamma) else {
            return Ok(None);
        };
        self.spend()?;
        Ok(Some(Work::Eval(Rc::new(fired), env.clone())))
    }
}

// ---------------------------------------------------------------------------
// Entry points
// ---------------------------------------------------------------------------

/// Evaluate a term in the **identity environment** of `gamma` — the root of
/// a conversion, where every local is its own neutral variable — to a
/// δ-transparent weak head value.
pub fn whnf_value<'v>(
    arena: &'v ValueArena<'v>,
    t: &Rc<Term>,
    gamma: &LocalCtx,
    defs: Defs<'_>,
    fuel: u64,
) -> Result<Rc<Val<'v>>, OutOfFuel> {
    let mut ev = Eval::new(fuel, defs, gamma.base, arena);
    let env = Env::identity(arena, gamma.entries.len() as u32);
    let v = ev.eval_tm(t, &env)?;
    ev.delta_whnf(v)
}

/// [`whnf_value`] for types.
pub fn whnf_value_ty<'v>(
    arena: &'v ValueArena<'v>,
    t: &Rc<Type>,
    gamma: &LocalCtx,
    defs: Defs<'_>,
    fuel: u64,
) -> Result<Rc<VTy<'v>>, OutOfFuel> {
    let mut ev = Eval::new(fuel, defs, gamma.base, arena);
    let env = Env::identity(arena, gamma.entries.len() as u32);
    let v = ev.eval_ty(t, &env)?;
    ev.delta_whnf_ty(v)
}

#[cfg(test)]
mod tests {
    use super::{nat_step_synchronizes, Elim, Eval};
    use crate::level::Level;
    use crate::reduce::{Defs, OutOfFuel};
    use crate::term::{CtxBase, LocalVar, Term, Type};
    use crate::value::program::ContextProgram;
    use crate::value::{Env, TmClo, TyClo, Val, ValueArena};
    use std::num::NonZeroU64;
    use std::rc::Rc;

    fn two_to_64() -> Rc<ContextProgram<()>> {
        let full = ContextProgram::run((), NonZeroU64::new(u64::MAX).unwrap());
        ContextProgram::prepend((), NonZeroU64::new(1).unwrap(), full)
    }

    fn shared_two_to_64() -> Rc<ContextProgram<()>> {
        let mut program = ContextProgram::run((), NonZeroU64::new(1).unwrap());
        for _ in 0..64 {
            program = ContextProgram::compose(Rc::clone(&program), program);
        }
        program
    }

    fn nat_elim<'v>(
        arena: &'v ValueArena<'v>,
        env: Env<'v>,
        step_body: Term,
    ) -> Elim<'v> {
        Elim::ElimNat {
            level: Level::Zero,
            motive: arena.ty(TyClo::new(env, Rc::new(Type::Nat))),
            base: arena.tm(TmClo::val(Rc::new(Val::Zero))),
            step: arena.tm(TmClo::syn(env, Rc::new(step_body))),
        }
    }

    fn dummy_lam(body: Term) -> Term {
        Term::Lam {
            dom_level: Level::Zero,
            cod_level: Level::Zero,
            dom: Rc::new(Type::Nat),
            body: Rc::new(body),
        }
    }

    fn synchronous_step() -> Term {
        dummy_lam(Term::ElimNat {
            level: Level::Zero,
            motive: Rc::new(Type::Nat),
            base: Rc::new(Term::Zero),
            step: Rc::new(Term::App {
                fun: Rc::new(Term::Var(LocalVar(3))),
                dom_level: Level::Zero,
                cod_level: Level::Zero,
                dom: Rc::new(Type::Nat),
                cod: Rc::new(Type::Nat),
                arg: Rc::new(Term::Var(LocalVar(1))),
            }),
            scrut: Rc::new(Term::Var(LocalVar(0))),
        })
    }

    fn app_elim<'v>(arena: &'v ValueArena<'v>, arg: &'v TmClo<'v>) -> Elim<'v> {
        let ty = arena.ty(TyClo::new(Env::empty(), Rc::new(Type::Nat)));
        Elim::App {
            dom_level: Level::Zero,
            cod_level: Level::Zero,
            dom: ty,
            cod: ty,
            arg,
        }
    }

    #[test]
    fn saturated_runs_present_two_to_64_as_one_successor_step() {
        let arena = ValueArena::new();
        let tail = arena.tm(TmClo::val(Rc::new(Val::Zero)));
        let program = two_to_64();
        let pred = Val::nat_run_pred(&arena, &program, tail);
        assert!(matches!(pred, TmClo::Val(v) if matches!(&**v, Val::NatRun { .. })));
    }

    #[test]
    fn maximum_literal_enters_the_value_domain_as_one_saturated_run() {
        let arena = ValueArena::new();
        let env = Env::empty();
        let mut ev = Eval::new(1, Defs::opaque(), CtxBase::Nil, &arena);
        let value = ev.eval_tm_ref(&Term::NatLit(u64::MAX), &env).unwrap();
        assert!(matches!(&*value,
            Val::NatRun { program, tail }
                if matches!(&**program,
                    ContextProgram::Run { count, .. } if count.get() == u64::MAX)
                && matches!(tail, TmClo::Val(z) if matches!(&**z, Val::Zero))));
    }

    #[test]
    fn successor_algebra_maps_a_shared_run_without_visiting_its_nodes() {
        let arena = ValueArena::new();
        let env = Env::empty();
        let tail = arena.tm(TmClo::val(Rc::new(Val::Zero)));
        let program = shared_two_to_64();
        let head = Rc::new(Val::NatRun { program: Rc::clone(&program), tail });
        let elim = nat_elim(
            &arena,
            env,
            Term::Succ(Rc::new(Term::Var(LocalVar(0)))),
        );
        let mut ev = Eval::new(2, Defs::opaque(), CtxBase::Nil, &arena);
        let result = ev.elim(head, elim).unwrap();
        assert!(matches!(&*result,
            Val::NatRun { program: mapped, .. } if Rc::ptr_eq(mapped, &program)));
    }

    /// `add`-shaped folds chain: mapping a run onto a tail whose fold is
    /// itself a run must yield one saturated run, not two fragments, or a
    /// doubled literal (`p + p`, and so `pow(2, k)`) is `2^k` fragments.
    #[test]
    fn successor_algebra_merges_the_run_its_tail_produces() {
        let arena = ValueArena::new();
        let env = Env::empty();
        let zero = arena.tm(TmClo::val(Rc::new(Val::Zero)));
        let inner = arena.tm(TmClo::val(Rc::new(Val::NatRun {
            program: ContextProgram::run((), NonZeroU64::new(4).unwrap()),
            tail: zero,
        })));
        let head = Rc::new(Val::NatRun {
            program: ContextProgram::run((), NonZeroU64::new(3).unwrap()),
            tail: inner,
        });
        let elim = nat_elim(
            &arena,
            env,
            Term::Succ(Rc::new(Term::Var(LocalVar(0)))),
        );
        let mut ev = Eval::new(8, Defs::opaque(), CtxBase::Nil, &arena);
        let result = ev.elim(head, elim).unwrap();
        assert!(matches!(&*result,
            Val::NatRun { program, .. }
                if matches!(&**program, ContextProgram::Run { count, .. } if count.get() == 7)));
    }

    /// `twice` is the successor algebra with two constructors per step: a
    /// saturated run's count is scaled, in constant work.
    #[test]
    fn double_successor_algebra_scales_a_saturated_run() {
        let arena = ValueArena::new();
        let env = Env::empty();
        let tail = arena.tm(TmClo::val(Rc::new(Val::Zero)));
        let head = Rc::new(Val::NatRun {
            program: ContextProgram::run((), NonZeroU64::new(1 << 40).unwrap()),
            tail,
        });
        let elim = nat_elim(
            &arena,
            env,
            Term::Succ(Rc::new(Term::Succ(Rc::new(Term::Var(LocalVar(0)))))),
        );
        let mut ev = Eval::new(4, Defs::opaque(), CtxBase::Nil, &arena);
        let result = ev.elim(head, elim).unwrap();
        assert!(matches!(&*result,
            Val::NatRun { program, .. }
                if matches!(&**program, ContextProgram::Run { count, .. } if count.get() == 1 << 41)));
    }

    /// A count the wider algebra cannot represent in one `u64` run is not
    /// guessed: the fold takes the ordinary one-step path and obeys fuel.
    #[test]
    fn double_successor_algebra_declines_an_overflowing_count() {
        let arena = ValueArena::new();
        let env = Env::empty();
        let tail = arena.tm(TmClo::val(Rc::new(Val::Zero)));
        let head = Rc::new(Val::NatRun {
            program: ContextProgram::run((), NonZeroU64::new(u64::MAX).unwrap()),
            tail,
        });
        let elim = nat_elim(
            &arena,
            env,
            Term::Succ(Rc::new(Term::Succ(Rc::new(Term::Var(LocalVar(0)))))),
        );
        let mut ev = Eval::new(16, Defs::opaque(), CtxBase::Nil, &arena);
        // The ordinary step exposes `su (su ih)` with the fold pending at
        // the predecessor, one logical step at a time; descending the
        // successors it produces is where fuel runs out, never a run.
        let mut cur = ev.elim(head, elim).unwrap();
        for _ in 0..64 {
            match &*cur {
                Val::Succ(inner) => match ev.force(inner) {
                    Ok(next) => cur = next,
                    Err(OutOfFuel) => return,
                },
                Val::NatRun { .. } => panic!("an overflowing count was scaled"),
                other => panic!("unexpected head: {other:?}"),
            }
        }
        panic!("fuel never ran out");
    }

    #[test]
    fn an_arbitrary_fold_over_a_shared_run_still_obeys_fuel() {
        let arena = ValueArena::new();
        let env = Env::empty();
        let tail = arena.tm(TmClo::val(Rc::new(Val::Zero)));
        let head = Rc::new(Val::NatRun { program: shared_two_to_64(), tail });
        // Return the induction hypothesis: observing the result genuinely
        // asks to traverse the logical spine, so compression must not claim
        // a constant-time answer.
        let elim = nat_elim(&arena, env, Term::Var(LocalVar(0)));
        let mut ev = Eval::new(32, Defs::opaque(), CtxBase::Nil, &arena);
        assert_eq!(ev.elim(head, elim).unwrap_err(), OutOfFuel);
    }

    #[test]
    fn synchronous_fold_cancels_independent_saturated_runs() {
        let arena = ValueArena::new();
        let env = Env::empty();
        let tail = arena.tm(TmClo::val(Rc::new(Val::Zero)));
        let left = Rc::new(Val::NatRun {
            program: ContextProgram::run((), NonZeroU64::new(u64::MAX).unwrap()),
            tail,
        });
        let right = arena.tm(TmClo::val(Rc::new(Val::NatRun {
            program: ContextProgram::run((), NonZeroU64::new(u64::MAX).unwrap()),
            tail,
        })));
        let elim = Elim::ElimNat {
            level: Level::Zero,
            motive: arena.ty(TyClo::new(env, Rc::new(Type::Nat))),
            base: arena.tm(TmClo::syn(env, Rc::new(dummy_lam(Term::Zero)))),
            step: arena.tm(TmClo::syn(env, Rc::new(synchronous_step()))),
        };
        let mut ev = Eval::new(8, Defs::opaque(), CtxBase::Nil, &arena);
        let folded = ev.elim(left, elim).unwrap();
        let result = ev.elim(folded, app_elim(&arena, right)).unwrap();
        assert!(matches!(&*result, Val::Zero));
    }

    #[test]
    fn synchronous_fold_bisimulates_independent_exponential_dags() {
        let arena = ValueArena::new();
        let env = Env::empty();
        let tail = arena.tm(TmClo::val(Rc::new(Val::Zero)));
        let left = Rc::new(Val::NatRun { program: shared_two_to_64(), tail });
        let right = arena.tm(TmClo::val(Rc::new(Val::NatRun {
            program: shared_two_to_64(),
            tail,
        })));
        let elim = Elim::ElimNat {
            level: Level::Zero,
            motive: arena.ty(TyClo::new(env, Rc::new(Type::Nat))),
            base: arena.tm(TmClo::syn(env, Rc::new(dummy_lam(Term::Zero)))),
            step: arena.tm(TmClo::syn(env, Rc::new(synchronous_step()))),
        };
        let mut ev = Eval::new(80, Defs::opaque(), CtxBase::Nil, &arena);
        let folded = ev.elim(left, elim).unwrap();
        let result = ev.elim(folded, app_elim(&arena, right)).unwrap();
        assert!(matches!(&*result, Val::Zero));
    }

    #[test]
    fn almost_synchronous_algebra_is_not_accelerated() {
        let env = Env::empty();
        let mut step = synchronous_step();
        let Term::Lam { body, .. } = &mut step else { unreachable!() };
        let Term::ElimNat { step: inner, .. } = Rc::make_mut(body) else { unreachable!() };
        let Term::App { fun, .. } = Rc::make_mut(inner) else { unreachable!() };
        *fun = Rc::new(Term::Var(LocalVar(0)));
        let closure = TmClo::syn(env, Rc::new(step));
        assert!(!nat_step_synchronizes(&closure));
    }
}
