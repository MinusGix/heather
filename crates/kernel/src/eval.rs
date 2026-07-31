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
//!   52 branch telescopes are not written down a sixth time.
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

use std::rc::Rc;

use crate::level::Level;
use crate::reduce::{beta_elim_ty, beta_elim_tm, step_type_delta, Defs, OutOfFuel, Rec};
use crate::subst::{GlobalEntry, GlobalSubst};
use crate::term::{
    nth, CtxBase, CtxEntry, GlobalVar, LocalCtx, LocalSubst, LocalVar, Term, Type,
};
use crate::value::{
    Elim, Env, Head, Lookup, TmClo, TyClo, VNeTy, VNeutral, VSubst, VTail, VTy, Val,
};

type Res<T> = Result<T, OutOfFuel>;

// ---------------------------------------------------------------------------
// Small constructors
// ---------------------------------------------------------------------------

fn tclo(env: &Env, t: &Rc<Term>) -> Rc<TmClo> {
    Rc::new(TmClo::syn(env.clone(), Rc::clone(t)))
}

fn yclo(env: &Env, t: &Rc<Type>) -> Rc<TyClo> {
    Rc::new(TyClo::new(env.clone(), Rc::clone(t)))
}

fn vclo(v: Rc<Val>) -> Rc<TmClo> {
    Rc::new(TmClo::val(v))
}

fn neutral(head: Head, spine: Vec<Elim>, unfold: Option<Rc<TmClo>>) -> Rc<Val> {
    Rc::new(Val::Neutral(Rc::new(VNeutral { head, spine, unfold })))
}

/// An eliminator applied to something it cannot eliminate. Unreachable on
/// well-typed input — `reduce.rs` is equally stuck there — but represented
/// rather than panicked on, so no input reaches undefined behaviour.
fn stuck(head: &Rc<Val>, e: &Elim) -> Rc<Val> {
    neutral(Head::Stuck(Rc::clone(head)), vec![e.clone()], None)
}

// ---------------------------------------------------------------------------
// The machine
// ---------------------------------------------------------------------------

/// A pending reduction, in the tail position of [`Eval::drive`]'s loop.
enum Work {
    /// Already a weak head value.
    Val(Rc<Val>),
    /// `eval(t, ρ)`.
    Eval(Rc<Term>, Env),
    /// Force a 0-binder sub-structure.
    Force(Rc<TmClo>),
    /// Apply a closure to its pending binders' values.
    Apply(Rc<TmClo>, Vec<Rc<TmClo>>),
    /// [`Work::Apply`] at one binder — β's commonest shape, and the one that
    /// must not allocate a vector to say so.
    Apply1(Rc<TmClo>, Rc<TmClo>),
    /// Eliminate a weak head value.
    Elim(Rc<Val>, Elim),
}

/// What a value flows back into: a thunk waiting to memoize it, or an
/// elimination waiting for its head.
enum Frame {
    Memo(Rc<TmClo>),
    Elim(Rc<Elim>),
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
pub struct Eval<'a> {
    fuel: u64,
    defs: Defs<'a>,
    base: CtxBase,
    /// [`Eval::drive`]'s continuation stack, kept across drives so that the
    /// common reduction step allocates nothing for it. Nested drives (a
    /// scrutinee evaluated before its elimination is built) use it as a
    /// stack of stacks: each records the height it entered at.
    frames: Vec<Frame>,
}

impl<'a> Eval<'a> {
    /// A run with `fuel` units, unfolding the definitions of `defs`, over a Γ
    /// whose base is `base`.
    pub fn new(fuel: u64, defs: Defs<'a>, base: CtxBase) -> Eval<'a> {
        Eval { fuel, defs, base, frames: Vec::new() }
    }

    /// The unspent budget.
    pub fn fuel(&self) -> u64 {
        self.fuel
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
    fn scope(&self, env: &Env) -> LocalCtx {
        LocalCtx {
            base: self.base,
            entries: vec![
                CtxEntry { ty: Rc::new(Type::Nat), level: Level::Zero };
                env.len() as usize
            ],
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
    fn drive(&mut self, start: Work) -> Res<Rc<Val>> {
        let floor = self.frames.len();
        let out = self.drive_from(start, floor);
        // An error unwinds whatever this drive had pending; a thunk that
        // never reached its frame keeps no memo (design §6).
        self.frames.truncate(floor);
        out
    }

    fn drive_from(&mut self, start: Work, floor: usize) -> Res<Rc<Val>> {
        let mut work = start;
        loop {
            work = match work {
                Work::Eval(t, env) => self.step_eval(&t, &env)?,
                Work::Elim(head, e) => self.step_elim(head, e)?,
                Work::Apply1(c, arg) => match &*c {
                    TmClo::Syn { env, body, .. } => {
                        Work::Eval(Rc::clone(body), env.push(arg))
                    }
                    _ => Work::Force(c),
                },
                Work::Apply(c, args) => match &*c {
                    TmClo::Syn { env, body, .. } => {
                        Work::Eval(Rc::clone(body), env.extend(&args))
                    }
                    // A closure position holding a computed value has no
                    // pending binders; it ignores them.
                    _ => Work::Force(c),
                },
                Work::Force(c) => {
                    if let Some(v) = c.memo() {
                        Work::Val(v)
                    } else {
                        match &*c {
                            TmClo::Val(v) => Work::Val(Rc::clone(v)),
                            TmClo::Syn { env, body, .. } => {
                                let w = Work::Eval(Rc::clone(body), env.clone());
                                self.frames.push(Frame::Memo(Rc::clone(&c)));
                                w
                            }
                            TmClo::Elim { head, elim, .. } => {
                                let w = Work::Force(Rc::clone(head));
                                self.frames.push(Frame::Memo(Rc::clone(&c)));
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
                            c.set_memo(&v);
                            Work::Val(v)
                        }
                        Some(Frame::Elim(e)) => Work::Elim(v, (*e).clone()),
                    }
                }
            };
        }
    }

    // -- forcing and application -------------------------------------------

    /// Force a 0-binder sub-structure to its weak head value. Memoizes on
    /// success only.
    pub fn force(&mut self, c: &Rc<TmClo>) -> Res<Rc<Val>> {
        self.drive(Work::Force(Rc::clone(c)))
    }

    /// [`Eval::force`] for types.
    pub fn force_ty(&mut self, c: &Rc<TyClo>) -> Res<Rc<VTy>> {
        if let Some(v) = c.memo() {
            return Ok(v);
        }
        let v = match &**c {
            TyClo::Val(v) => Rc::clone(v),
            TyClo::Syn { env, body, .. } => {
                let (env, body) = (env.clone(), Rc::clone(body));
                self.eval_ty(&body, &env)?
            }
            TyClo::Vec { level, elem, len, .. } => {
                let (level, elem, len) = (level.clone(), Rc::clone(elem), Rc::clone(len));
                let lv = self.force(&len)?;
                self.vec_ty(&level, elem, &lv)?
            }
            TyClo::El { level, tm, .. } => {
                let (level, tm) = (level.clone(), Rc::clone(tm));
                let v = self.force(&tm)?;
                self.decode(&level, &v)?
            }
        };
        c.set_memo(&v);
        Ok(v)
    }

    /// Apply a closure to its pending binders' values, `args[0]` outermost.
    /// This is the operation that replaces `apply_local`: it allocates one
    /// environment cell per binder and copies nothing.
    pub fn apply(&mut self, c: &Rc<TmClo>, args: &[Rc<TmClo>]) -> Res<Rc<Val>> {
        let w = match args {
            [a] => Work::Apply1(Rc::clone(c), Rc::clone(a)),
            _ => Work::Apply(Rc::clone(c), args.to_vec()),
        };
        self.drive(w)
    }

    /// [`Eval::apply`] for type closures. A closure that is not syntactic has
    /// no pending binders and ignores them (`TyClo::Val` is a *constant*
    /// closure — the shape conversion's weakened annotations take).
    pub fn apply_ty(&mut self, c: &Rc<TyClo>, args: &[Rc<TmClo>]) -> Res<Rc<VTy>> {
        if args.is_empty() {
            return self.force_ty(c);
        }
        match &**c {
            TyClo::Syn { env, body, .. } => {
                let (env, body) = (env.extend(args), Rc::clone(body));
                self.eval_ty(&body, &env)
            }
            _ => self.force_ty(c),
        }
    }

    // -- δ ------------------------------------------------------------------

    /// Force the glued unfoldings at the head until the value is not a
    /// definition's spine — i.e. the δ-transparent weak head value.
    ///
    /// Conversion's δ-lazy stage deliberately does *not* call this until the
    /// opaque comparison has failed (design §5); it is the second stage, and
    /// the differential oracle's counterpart to `whnf_term_delta`.
    pub fn delta_whnf(&mut self, mut v: Rc<Val>) -> Res<Rc<Val>> {
        loop {
            let unfold = match &*v {
                Val::Neutral(n) => n.unfold.as_ref().map(Rc::clone),
                _ => None,
            };
            match unfold {
                None => return Ok(v),
                Some(u) => {
                    self.spend()?;
                    v = self.force(&u)?;
                }
            }
        }
    }

    /// [`Eval::delta_whnf`] for types: a type is δ-stuck only through `El`
    /// (type-level globals carry no body) or through a `Vec`/`Fin` length.
    pub fn delta_whnf_ty(&mut self, mut v: Rc<VTy>) -> Res<Rc<VTy>> {
        enum Next {
            Done,
            El(Level, Rc<Val>),
            Vec(Level, Rc<TyClo>, Rc<Val>),
            Fin(Rc<Val>),
        }
        loop {
            let next = match &*v {
                VTy::Neutral(VNeTy::El { level, tm }) => Next::El(level.clone(), Rc::clone(tm)),
                VTy::Vec { level, elem, len } => {
                    Next::Vec(level.clone(), Rc::clone(elem), Rc::clone(len))
                }
                VTy::Fin { len } => Next::Fin(Rc::clone(len)),
                _ => Next::Done,
            };
            match next {
                Next::Done => return Ok(v),
                Next::El(level, tm) => {
                    let d = self.delta_whnf(Rc::clone(&tm))?;
                    if Rc::ptr_eq(&d, &tm) {
                        return Ok(v);
                    }
                    v = self.decode(&level, &d)?;
                }
                Next::Vec(level, elem, len) => {
                    let d = self.delta_whnf(Rc::clone(&len))?;
                    if Rc::ptr_eq(&d, &len) {
                        return Ok(v);
                    }
                    v = self.vec_ty(&level, elem, &d)?;
                }
                Next::Fin(len) => {
                    let d = self.delta_whnf(Rc::clone(&len))?;
                    if Rc::ptr_eq(&d, &len) {
                        return Ok(v);
                    }
                    v = self.fin_ty(&d)?;
                }
            }
        }
    }

    // -- types --------------------------------------------------------------

    /// Evaluate a type to a weak head normal type value.
    pub fn eval_ty(&mut self, t: &Type, env: &Env) -> Res<Rc<VTy>> {
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
    fn decode(&mut self, level: &Level, v: &Rc<Val>) -> Res<Rc<VTy>> {
        /// `El^l c` as a lazy type. When `c` has syntax the `El` is built as
        /// syntax over the child's own closure — one step deep, so a decoded
        /// `Π`'s domain is not reduced until someone asks; otherwise the
        /// domain's own lazy `El` says the same thing about a value.
        fn el(l: &Level, c: &Rc<TmClo>) -> Option<Rc<TyClo>> {
            Some(Rc::new(match c.as_syn() {
                Some((env, body)) => TyClo::new(
                    env.clone(),
                    Rc::new(Type::El { level: l.clone(), tm: Rc::clone(body) }),
                ),
                None => TyClo::el(l.clone(), Rc::clone(c)),
            }))
        }
        let stuck_el =
            || Ok(Rc::new(VTy::Neutral(VNeTy::El { level: level.clone(), tm: Rc::clone(v) })));

        let decoded = match &**v {
            Val::TmNat => VTy::Nat,
            Val::TmTy(l) => VTy::Ty(l.clone()),
            Val::TmUnit { level } => VTy::Unit { level: level.clone() },
            Val::TmEmpty { level } => VTy::Empty { level: level.clone() },
            Val::TmSEmpty { level } => VTy::SEmpty { level: level.clone() },
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
                    lhs: Rc::clone(lhs),
                    rhs: Rc::clone(rhs),
                }
            }
            Val::TmSEq { level: l, ty, lhs, rhs } => {
                let Some(t) = el(l, ty) else { return stuck_el() };
                VTy::SEq {
                    level: l.clone(),
                    ty: t,
                    lhs: Rc::clone(lhs),
                    rhs: Rc::clone(rhs),
                }
            }
            // The arity rides across unchanged: it is a term under the same
            // binder, and only the shape decodes.
            Val::TmWf { level: l, shape, arity } => {
                let Some(s) = el(l, shape) else { return stuck_el() };
                VTy::Wf { level: l.clone(), shape: s, arity: Rc::clone(arity) }
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
        elem: Rc<TyClo>,
        len: &Rc<Val>,
    ) -> Res<Rc<VTy>> {
        let out = match &**len {
            Val::Zero => {
                self.spend()?;
                VTy::Unit { level: level.clone() }
            }
            Val::Succ(pred) => {
                self.spend()?;
                let tail = TyClo::vec(level.clone(), Rc::clone(&elem), Rc::clone(pred));
                VTy::Sigma {
                    fst_level: level.clone(),
                    snd_level: level.clone(),
                    fst: Rc::clone(&elem),
                    snd: Rc::new(tail),
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
    fn fin_ty(&mut self, len: &Rc<Val>) -> Res<Rc<VTy>> {
        let out = match &**len {
            Val::Zero => {
                self.spend()?;
                VTy::Empty { level: Level::Zero }
            }
            Val::Succ(pred) => {
                self.spend()?;
                let rhs_env = Env::empty().push(Rc::clone(pred));
                VTy::Sum {
                    lhs_level: Level::Zero,
                    rhs_level: Level::Zero,
                    lhs: Rc::new(TyClo::new(
                        Env::empty(),
                        Rc::new(Type::Unit { level: Level::Zero }),
                    )),
                    rhs: Rc::new(TyClo::new(
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
    fn eval_subst(&mut self, d: &LocalSubst, env: &Env) -> Res<VSubst> {
        let mut terms = Vec::with_capacity(d.terms.len());
        for t in &d.terms {
            terms.push(self.eval_tm(t, env)?);
        }
        Ok(VSubst { tail: VTail::of(d.tail, self.base), terms })
    }

    // -- terms --------------------------------------------------------------

    /// Evaluate a term to a weak head normal value.
    pub fn eval_tm(&mut self, t: &Rc<Term>, env: &Env) -> Res<Rc<Val>> {
        self.eval_tm_ref(t, env)
    }

    /// [`Eval::eval_tm`] on a node the caller does not own — the **root** of a
    /// conversion, which is syntax lent to the checker. Wrapping it in an
    /// `Rc` just to start the machine cost 1.3× on `nat/check-numeral`, whose
    /// every conversion is one `Nat ≈ Nat`.
    pub fn eval_tm_ref(&mut self, t: &Term, env: &Env) -> Res<Rc<Val>> {
        let w = self.step_eval(t, env)?;
        self.drive(w)
    }

    /// One step of [`Eval::eval_tm`], with its **tail positions returned**
    /// rather than called: see [`Eval::drive`].
    fn step_eval(&mut self, t: &Term, env: &Env) -> Res<Work> {
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
    fn global_tm(&mut self, var: GlobalVar, subst: VSubst) -> Rc<Val> {
        let unfold = self.defs.body(var).map(|body| {
            let mut denv = Env::empty();
            for v in &subst.terms {
                denv = denv.push(vclo(Rc::clone(v)));
            }
            Rc::new(TmClo::syn(denv, Rc::new(body)))
        });
        neutral(Head::Global { var, subst }, Vec::new(), unfold)
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
    pub fn elim(&mut self, head: Rc<Val>, e: Elim) -> Res<Rc<Val>> {
        self.drive(Work::Elim(head, e))
    }

    /// One step of [`Eval::elim`]; see [`Eval::drive`].
    fn step_elim(&mut self, head: Rc<Val>, e: Elim) -> Res<Work> {
        if let Val::Neutral(n) = &*head {
            let n = Rc::clone(n);
            return Ok(Work::Val(self.push_elim(&n, e)));
        }
        match (&*head, &e) {
            (Val::Lam { body, .. }, Elim::App { arg, .. }) => {
                self.spend()?;
                let (body, arg) = (Rc::clone(body), Rc::clone(arg));
                Ok(Work::Apply1(body, arg))
            }
            (Val::ULam { num_vars, body, .. }, Elim::UApp { levels })
                if *num_vars as usize == levels.len() =>
            {
                self.spend()?;
                let Some((benv, bbody)) = body.as_syn() else { return Ok(Work::Val(stuck(&head, &e))) };
                // The written vectors pair positionally (outermost first);
                // instantiation wants innermost-first.
                let phi: Vec<Level> = levels.iter().rev().cloned().collect();
                let (benv, inst) = (benv.clone(), Rc::new(bbody.inst_univ(&phi)));
                Ok(Work::Eval(inst, benv))
            }
            (Val::CtxLam { body, .. }, Elim::CtxApp { ctx }) => {
                self.spend()?;
                let Some((benv, bbody)) = body.as_syn() else { return Ok(Work::Val(stuck(&head, &e))) };
                let sigma = GlobalSubst::single(GlobalEntry::Ctx(ctx.clone()));
                let (benv, inst) = (benv.clone(), Rc::new(bbody.apply_global(&sigma)));
                Ok(Work::Eval(inst, benv))
            }
            (Val::TyLam { body, .. }, Elim::TyApp { arg }) => {
                self.spend()?;
                let Some((benv, bbody)) = body.as_syn() else { return Ok(Work::Val(stuck(&head, &e))) };
                let sigma = GlobalSubst::single(GlobalEntry::Ty(Rc::clone(arg)));
                let (benv, inst) = (benv.clone(), Rc::new(bbody.apply_global(&sigma)));
                Ok(Work::Eval(inst, benv))
            }
            (Val::Zero, Elim::ElimNat { base, .. }) => {
                self.spend()?;
                let base = Rc::clone(base);
                Ok(Work::Force(base))
            }
            // `elim_Nat … (su t) ⇝ s'[t/x, elim_Nat … t/y]`: the induction
            // hypothesis is a *pending* elimination, so a step that ignores
            // it costs nothing.
            (Val::Succ(pred), Elim::ElimNat { step, .. }) => {
                self.spend()?;
                let (pred, step) = (Rc::clone(pred), Rc::clone(step));
                let ih = Rc::new(TmClo::elim(Rc::clone(&pred), Rc::new(e.clone())));
                Ok(Work::Apply(step, vec![pred, ih]))
            }
            (Val::Refl { .. }, Elim::J { case, .. }) => {
                self.spend()?;
                let case = Rc::clone(case);
                Ok(Work::Force(case))
            }
            (Val::SRefl { .. }, Elim::Transp { tm, .. }) => {
                self.spend()?;
                let tm = Rc::clone(tm);
                Ok(Work::Force(tm))
            }
            (Val::Pair { fst, .. }, Elim::Fst { .. }) => {
                self.spend()?;
                let fst = Rc::clone(fst);
                Ok(Work::Force(fst))
            }
            (Val::Pair { snd, .. }, Elim::Snd { .. }) => {
                self.spend()?;
                let snd = Rc::clone(snd);
                Ok(Work::Force(snd))
            }
            (Val::Inl { val, .. }, Elim::Case { case_l, .. }) => {
                self.spend()?;
                let (val, case_l) = (Rc::clone(val), Rc::clone(case_l));
                Ok(Work::Apply1(case_l, val))
            }
            (Val::Inr { val, .. }, Elim::Case { case_r, .. }) => {
                self.spend()?;
                let (val, case_r) = (Rc::clone(val), Rc::clone(case_r));
                Ok(Work::Apply1(case_r, val))
            }
            (Val::Sup { label, children, .. }, Elim::ElimW { .. }) => {
                self.spend()?;
                let (label, children) = (Rc::clone(label), Rc::clone(children));
                match self.fire_elim_w(&label, &children, &e)? {
                    Some(v) => Ok(v),
                    None => Ok(Work::Val(stuck(&head, &e))),
                }
            }
            (Val::Supf { label, children, .. }, Elim::ElimWf { .. }) => {
                self.spend()?;
                let (label, children) = (Rc::clone(label), Rc::clone(children));
                match self.fire_elim_wf(&label, &children, &e)? {
                    Some(v) => Ok(v),
                    None => Ok(Work::Val(stuck(&head, &e))),
                }
            }
            (Val::BoxTy(code), Elim::LetBoxTy { body, .. }) => {
                self.spend()?;
                let Some((benv, bbody)) = body.as_syn() else { return Ok(Work::Val(stuck(&head, &e))) };
                let sigma = GlobalSubst::single(GlobalEntry::Ty(Rc::clone(code)));
                let (benv, inst) = (benv.clone(), Rc::new(bbody.apply_global(&sigma)));
                Ok(Work::Eval(inst, benv))
            }
            (Val::BoxTm(code), Elim::LetBoxTm { body, .. }) => {
                self.spend()?;
                let Some((benv, bbody)) = body.as_syn() else { return Ok(Work::Val(stuck(&head, &e))) };
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
                        vec![e.clone()],
                        None,
                    )));
                }
                let code = Rc::clone(code);
                match self.fire_code_ty(&code, &e)? {
                    Some(v) => Ok(v),
                    None => Ok(Work::Val(stuck(&head, &e))),
                }
            }
            (Val::BoxTm(code), Elim::ElimCodeTm { .. }) => {
                if matches!(&**code, Term::GlobalTm { .. }) {
                    return Ok(Work::Val(neutral(
                        Head::BoxedGlobalTm(Rc::clone(code)),
                        vec![e.clone()],
                        None,
                    )));
                }
                let code = Rc::clone(code);
                match self.fire_code_tm(&code, &e)? {
                    Some(v) => Ok(v),
                    None => Ok(Work::Val(stuck(&head, &e))),
                }
            }
            _ => Ok(Work::Val(stuck(&head, &e))),
        }
    }

    /// Extend a neutral's spine — and, when it is glued, its pending
    /// unfolding by the same elimination, so that forcing the unfolding
    /// replays the spine (design §5).
    fn push_elim(&mut self, n: &Rc<VNeutral>, e: Elim) -> Rc<Val> {
        let unfold = n
            .unfold
            .as_ref()
            .map(|u| Rc::new(TmClo::elim(Rc::clone(u), Rc::new(e.clone()))));
        let mut spine = n.spine.clone();
        spine.push(e);
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
        label: &Rc<TmClo>,
        children: &Rc<TmClo>,
        e: &Elim,
    ) -> Res<Option<Work>> {
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
        let rho_af = env.push(Rc::clone(label)).push(Rc::clone(children));
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
            dom: Rc::new(TyClo::new(rho_af.clone(), Rc::new(pos_body.shift_local(1)))),
            body: Rc::new(TmClo::syn(rho_af, Rc::new(rec))),
        });
        let step = Rc::clone(step);
        Ok(Some(Work::Apply(
            step,
            vec![Rc::clone(label), Rc::clone(children), vclo(ih)],
        )))
    }

    /// `elim_Wf (sup_f(…; a; cs)) ⇝ s[a, cs, λ i. elim_Wf(…; nth … cs i)]`.
    /// [`fire_elim_w`](Eval::fire_elim_w)'s construction, with the child
    /// reached through the shared [`nth`] schema instead of an application.
    fn fire_elim_wf(
        &mut self,
        label: &Rc<TmClo>,
        children: &Rc<TmClo>,
        e: &Elim,
    ) -> Res<Option<Work>> {
        let Elim::ElimWf { level, motive_level, shape, arity, motive, step, env } = e else {
            return Ok(None);
        };
        let Some((_, step_body)) = step.as_syn() else { return Ok(None) };
        let Some((_, arity_body)) = arity.as_syn() else { return Ok(None) };
        let (Some((_, shape_body)), Some((_, motive_body))) = (shape.as_syn(), motive.as_syn())
        else {
            return Ok(None);
        };
        let rho_acs = env.push(Rc::clone(label)).push(Rc::clone(children));
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
            dom: Rc::new(TyClo::new(
                rho_acs.clone(),
                Rc::new(Type::Fin { len: Rc::new(arity_body.shift_local(1)) }),
            )),
            body: Rc::new(TmClo::syn(rho_acs, Rc::new(rec))),
        });
        let step = Rc::clone(step);
        Ok(Some(Work::Apply(
            step,
            vec![Rc::clone(label), Rc::clone(children), vclo(ih)],
        )))
    }

    /// `elim^Typ … (box code)`: the fired branch comes from the *shared*
    /// [`beta_elim_ty`] as syntax in the current Γ, and is then evaluated in
    /// the current environment. `None` is `reduce.rs`'s own stuck case (a
    /// layer-m type that cannot be code).
    fn fire_code_ty(&mut self, code: &Rc<Type>, e: &Elim) -> Res<Option<Work>> {
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
    fn fire_code_tm(&mut self, code: &Rc<Term>, e: &Elim) -> Res<Option<Work>> {
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
pub fn whnf_value(
    t: &Rc<Term>,
    gamma: &LocalCtx,
    defs: Defs<'_>,
    fuel: u64,
) -> Result<Rc<Val>, OutOfFuel> {
    let mut ev = Eval::new(fuel, defs, gamma.base);
    let env = Env::identity(gamma.entries.len() as u32);
    let v = ev.eval_tm(t, &env)?;
    ev.delta_whnf(v)
}

/// [`whnf_value`] for types.
pub fn whnf_value_ty(
    t: &Rc<Type>,
    gamma: &LocalCtx,
    defs: Defs<'_>,
    fuel: u64,
) -> Result<Rc<VTy>, OutOfFuel> {
    let mut ev = Eval::new(fuel, defs, gamma.base);
    let env = Env::identity(gamma.entries.len() as u32);
    let v = ev.eval_ty(t, &env)?;
    ev.delta_whnf_ty(v)
}
