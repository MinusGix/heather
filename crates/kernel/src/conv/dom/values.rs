//! The **value instantiation** of [`Dom`]: conversion over the environment
//! machine (docs/nbe-conversion-design.md §13, stage 2b).
//!
//! A weak head normal form is a [`Val`]/[`VTy`], and a sub-structure is a
//! closure. Two numbers travel with every sub-structure, and they are what
//! makes the shared arms typecheck against a domain where weakening is free
//! and instantiation is not:
//!
//! - **`home`** — the Γ-length of the scope the closure is written in;
//! - **`sat`** — the Γ-length at which it *is* a type (or a term), so that
//!   `sat - home` binders are still pending.
//!
//! The syntax domain conflates the two, because de Bruijn arithmetic does:
//! `t.shift_local(2)` both weakens `t` past two binders and leaves it a
//! perfectly good body under them. At values those are different operations —
//! weakening costs nothing (variables are levels) while a pending binder
//! costs an environment cell — so a carrier that says only "one binder deep"
//! is ambiguous the moment the scope it came from is not the scope it is read
//! in. `elim_W`'s step telescope is where that bites: it weakens the `W` type
//! by two and then reads it as a codomain under one more binder.
//!
//! Everything else follows the trait's own account. Two things are worth
//! naming because they are where this instantiation stops being mechanical:
//!
//! - [`Values::wf_step_telescope`] and the two motive instantiations do *not*
//!   rebuild ch. 04's schemas out of domain constructors. They take the
//!   closure's own `(environment, syntax)` apart, hand the **syntax** to the
//!   shared function in [`crate::term`] / [`crate::rec`], and evaluate the
//!   result in that same environment extended by the freshly pushed binders.
//!   The schemas are one source shared with `typing.rs`; a value-domain
//!   transcription would be a seventh copy of `nth` and a place for the two
//!   to drift.
//! - The layer-m arms weaken L or Ψ, and a captured environment does not
//!   weaken itself: [`Values::under_tele_ty`] is where `value::shift` is
//!   paid, and it is paid only there.

use std::rc::Rc;

use crate::eval::Eval;
use crate::level::Level;
use crate::rec;
use crate::subst::{GlobalEntry, GlobalSubst};
use crate::term::{
    wf_step_telescope, CtxEntries, CtxEntry, GlobalVar, LocalCtx, LocalVar, Term, Type,
};
use crate::value::{
    self, shift::Outer, Elim, Head, TmClo, TyClo, VNeTy, VNeutral, VSubst, VTy, Val,
};

use super::super::{Conv, Env, R, NC};
use super::{Dom, TmView, TyView};

/// The value domain: `Conv<'v, Values>` is the kernel's conversion checker.
pub(crate) struct Values;

// ---------------------------------------------------------------------------
// Carriers
// ---------------------------------------------------------------------------

/// A type sub-structure: a closure plus the two scope lengths of the module
/// docs.
#[derive(Clone)]
pub(crate) struct TyC<'v> {
    clo: &'v TyClo<'v>,
    home: u32,
    sat: u32,
}

/// [`TyC<'v>`] for terms.
#[derive(Clone)]
pub(crate) struct TmC<'v> {
    clo: &'v TmClo<'v>,
    home: u32,
    sat: u32,
}

/// The scope a code recursor's Γ-scoped raw syntax is read in: the
/// environment the elimination stored when it was built.
#[derive(Clone)]
pub(crate) struct RecEnv<'v>(value::Env<'v>);

fn glen<'v>(env: &Env<'v>) -> u32 {
    env.gamma.entries.len() as u32
}

/// The neutral variable a binder pushed at Γ-length `level` is bound to.
fn fresh<'v>(env: &value::Env<'v>, level: u32) -> &'v TmClo<'v> {
    env.arena().tm(TmClo::val(Rc::new(Val::var(level))))
}

/// The same variable, taken from the environment that already holds it
/// rather than allocated again — `open_*` asks for it once per binder
/// descent, which is conversion's hottest path.
fn var_at<'v>(env: &Env<'v>, level: u32) -> &'v TmClo<'v> {
    let n = env.gamma.entries.len() as u32;
    match n.checked_sub(1 + level).map(|i| env.rho.lookup(i)) {
        Some(value::Lookup::Bound(c)) => c,
        _ => fresh(&env.rho, level),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::num::NonZeroU64;

    fn doubling_nat(
        leaf_count: u64,
        depth: u32,
    ) -> Rc<value::program::ContextProgram<()>> {
        let mut program = value::program::ContextProgram::run(
            (),
            NonZeroU64::new(leaf_count).unwrap(),
        );
        for _ in 0..depth {
            program = value::program::ContextProgram::compose(Rc::clone(&program), program);
        }
        program
    }

    fn nat_run<'v>(
        arena: &'v value::ValueArena<'v>,
        program: Rc<value::program::ContextProgram<()>>,
        tail: &'v TmClo<'v>,
    ) -> TmC<'v> {
        TmC {
            clo: arena.tm(TmClo::val(Rc::new(Val::NatRun { program, tail }))),
            home: 0,
            sat: 0,
        }
    }

    fn compare_nat_runs(
        left: Rc<value::program::ContextProgram<()>>,
        right: Rc<value::program::ContextProgram<()>>,
        fuel: u64,
    ) -> R {
        let psi = crate::term::GlobalCtx::default();
        let gamma = LocalCtx::nil();
        let arena = value::ValueArena::new();
        let env = Env::new(&arena, &psi, &gamma, crate::layer::Layer::Prog);
        let tail = arena.tm(TmClo::val(Rc::new(Val::Zero)));
        let left = nat_run(&arena, left, tail);
        let right = nat_run(&arena, right, tail);
        let ty = TyC::value(&env, Rc::new(VTy::Nat));
        Conv::<Values>::new(fuel, &psi).tm(&env, &left, &right, &ty, &Level::Zero)
    }

    #[test]
    fn type_identity_fast_path_is_scope_sensitive() {
        let arena = value::ValueArena::new();
        let body = Type::El {
            level: Level::Zero,
            tm: Rc::new(Term::Var(LocalVar(0))),
        };
        let clo = arena.ty(TyClo::new(value::Env::empty(&arena), Rc::new(body)));
        let a = TyC { clo, home: 2, sat: 3 };
        let same = TyC { clo, home: 2, sat: 3 };
        let other_home = TyC { clo, home: 1, sat: 3 };
        let other_sat = TyC { clo, home: 2, sat: 4 };

        assert!(Values::ty_eq_fast(&a, &same));
        assert!(!Values::ty_eq_fast(&a, &other_home));
        assert!(!Values::ty_eq_fast(&a, &other_sat));
    }

    #[test]
    fn syntactic_closure_fast_path_needs_same_env_and_equal_body() {
        let arena = value::ValueArena::new();
        let body = || {
            Rc::new(Type::El { level: Level::Zero, tm: Rc::new(Term::Var(LocalVar(0))) })
        };
        let rho = value::Env::empty(&arena).push(fresh(&value::Env::empty(&arena), 0));
        let a = TyC { clo: arena.ty(TyClo::new(rho, body())), home: 2, sat: 3 };

        // Distinct closures, same environment spine, α-equal bodies: a hit.
        let equal = TyC { clo: arena.ty(TyClo::new(rho, body())), home: 2, sat: 3 };
        assert!(Values::ty_eq_fast(&a, &equal));

        // A different environment need not denote the same type, even with
        // an equal body — and equal *content* under a different spine node
        // is deliberately not inspected (the head pointer is the test).
        let other_env = TyC {
            clo: arena.ty(TyClo::new(
                value::Env::empty(&arena).push(fresh(&value::Env::empty(&arena), 0)),
                body(),
            )),
            home: 2,
            sat: 3,
        };
        assert!(!Values::ty_eq_fast(&a, &other_env));

        // A different body is never a hit; scope metadata still gates.
        let other_body = TyC { clo: arena.ty(TyClo::new(rho, Rc::new(Type::Nat))), home: 2, sat: 3 };
        assert!(!Values::ty_eq_fast(&a, &other_body));
        let other_scope = TyC { clo: arena.ty(TyClo::new(rho, body())), home: 2, sat: 4 };
        assert!(!Values::ty_eq_fast(&a, &other_scope));

        // The term side takes the same shortcut.
        let t = || Rc::new(Term::Succ(Rc::new(Term::Var(LocalVar(0)))));
        let rho = value::Env::empty(&arena).push(fresh(&value::Env::empty(&arena), 0));
        let ta = TmC { clo: arena.tm(TmClo::syn(rho, t())), home: 2, sat: 3 };
        let tb = TmC { clo: arena.tm(TmClo::syn(rho, t())), home: 2, sat: 3 };
        assert!(Values::tm_identity_fast(&ta, &tb));
    }

    #[test]
    fn term_identity_fast_path_is_scope_sensitive() {
        let arena = value::ValueArena::new();
        let body = Term::Succ(Rc::new(Term::Zero));
        let clo = arena.tm(TmClo::syn(value::Env::empty(&arena), Rc::new(body)));
        let a = TmC { clo, home: 2, sat: 3 };
        let same = TmC { clo, home: 2, sat: 3 };
        let other_home = TmC { clo, home: 1, sat: 3 };
        let other_sat = TmC { clo, home: 2, sat: 4 };

        assert!(Values::tm_identity_fast(&a, &same));
        assert!(!Values::tm_identity_fast(&a, &other_home));
        assert!(!Values::tm_identity_fast(&a, &other_sat));

        let psi = crate::term::GlobalCtx::default();
        let gamma = LocalCtx::nil();
        let arena = value::ValueArena::new();
        let env = Env::new(&arena, &psi, &gamma, crate::layer::Layer::Prog);
        let ty = TyC::value(&env, Rc::new(VTy::Nat));
        assert_eq!(Conv::<Values>::new(1, &psi).tm(&env, &a, &same, &ty, &Level::Zero), Ok(()));
        assert_eq!(
            Conv::<Values>::new(1, &psi).tm(&env, &a, &other_home, &ty, &Level::Zero),
            Err(crate::conv::ConvError::OutOfFuel)
        );
    }

    #[test]
    fn one_shared_nat_program_is_reflexive_without_expansion() {
        let arena = value::ValueArena::new();
        let tail = arena.tm(TmClo::val(Rc::new(Val::Zero)));
        let leaf = value::program::ContextProgram::run(
            (),
            NonZeroU64::new(u64::MAX).unwrap(),
        );
        let program = value::program::ContextProgram::compose(
            Rc::clone(&leaf),
            Rc::clone(&leaf),
        );
        let left = TmC {
            clo: arena.tm(TmClo::val(Rc::new(Val::NatRun {
                program: Rc::clone(&program),
                tail,
            }))),
            home: 0,
            sat: 0,
        };
        let right = TmC {
            clo: arena.tm(TmClo::val(Rc::new(Val::NatRun { program, tail }))),
            home: 0,
            sat: 0,
        };
        assert!(Values::tm_eq_fast(&left, &right));
    }

    #[test]
    fn independently_allocated_exponential_nat_dags_convert() {
        assert_eq!(compare_nat_runs(doubling_nat(1, 64), doubling_nat(1, 64), 80), Ok(()));
    }

    #[test]
    fn exponential_nat_prefix_preserves_unequal_residual_verdict() {
        let left = value::program::ContextProgram::compose(
            doubling_nat(1, 64),
            value::program::ContextProgram::run((), NonZeroU64::new(1).unwrap()),
        );
        let right = value::program::ContextProgram::compose(
            doubling_nat(1, 64),
            value::program::ContextProgram::run((), NonZeroU64::new(2).unwrap()),
        );
        assert_eq!(
            compare_nat_runs(left, right, 96),
            Err(crate::conv::ConvError::NotConvertible),
        );
    }

    #[test]
    fn hostile_near_match_obeys_conversion_fuel() {
        assert_eq!(
            compare_nat_runs(doubling_nat(1, 64), doubling_nat(2, 64), 16),
            Err(crate::conv::ConvError::OutOfFuel),
        );
    }
}

impl<'v> TyC<'v> {
    /// A sub-structure that is a type **here**, in `env`.
    fn here(env: &Env<'v>, clo: &'v TyClo<'v>) -> TyC<'v> {
        let n = glen(env);
        TyC { clo, home: n, sat: n }
    }

    /// A sub-structure under `k` of the carrier's own pending binders.
    fn under(env: &Env<'v>, clo: &'v TyClo<'v>, k: u32) -> TyC<'v> {
        let n = glen(env);
        TyC { clo, home: n, sat: n + k }
    }

    fn value(env: &Env<'v>, v: Rc<VTy<'v>>) -> TyC<'v> {
        TyC::here(env, env.rho.arena().ty(TyClo::val(v)))
    }
}

impl<'v> TmC<'v> {
    fn here(env: &Env<'v>, clo: &'v TmClo<'v>) -> TmC<'v> {
        let n = glen(env);
        TmC { clo, home: n, sat: n }
    }

    fn under(env: &Env<'v>, clo: &'v TmClo<'v>, k: u32) -> TmC<'v> {
        let n = glen(env);
        TmC { clo, home: n, sat: n + k }
    }

    fn value(env: &Env<'v>, v: Rc<Val<'v>>) -> TmC<'v> {
        TmC::here(env, env.rho.arena().tm(TmClo::val(v)))
    }
}

/// Apply a type closure to arguments, **without forcing**: a syntactic
/// closure extends its environment, anything else has no pending binders and
/// ignores them.
fn apply_ty_clo<'v>(c: &'v TyClo<'v>, args: &[&'v TmClo<'v>]) -> &'v TyClo<'v> {
    if args.is_empty() {
        return c;
    }
    match c {
        TyClo::Syn { env, body, .. } => {
            env.arena().ty(TyClo::new(env.extend(args), Rc::clone(body)))
        }
        _ => c,
    }
}

fn apply_tm_clo<'v>(c: &'v TmClo<'v>, args: &[&'v TmClo<'v>]) -> &'v TmClo<'v> {
    if args.is_empty() {
        return c;
    }
    match c {
        TmClo::Syn { env, body, .. } => {
            env.arena().tm(TmClo::syn(env.extend(args), Rc::clone(body)))
        }
        _ => c,
    }
}

/// Make a closure consume — and ignore — `by` more binders, innermost. This
/// is what `shift_local` means on the syntax side, and the reason it is a
/// shift *there* and a nothing *here* is that the body's own free indices
/// have to step over the new cells.
fn weaken_ty_clo<'v>(c: &'v TyClo<'v>, by: u32) -> &'v TyClo<'v> {
    if by == 0 {
        return c;
    }
    match c {
        TyClo::Syn { env, body, .. } => {
            env.arena().ty(TyClo::new(*env, Rc::new(body.shift_local(by))))
        }
        _ => c,
    }
}

fn weaken_tm_clo<'v>(c: &'v TmClo<'v>, by: u32) -> &'v TmClo<'v> {
    if by == 0 {
        return c;
    }
    match c {
        TmClo::Syn { env, body, .. } => {
            env.arena().tm(TmClo::syn(*env, Rc::new(body.shift_local(by))))
        }
        _ => c,
    }
}

/// Read a carrier in `env` with `pending` of its binders left for the caller:
/// supply the fresh neutrals of every binder between the carrier's home and
/// that point, weakening first if the carrier is older than the scope.
///
/// This is the one place the two numbers are spent, and it is total by
/// construction: `k` args are supplied for levels `home .. home + k`, which
/// are exactly the levels [`Env<'v>::push_entry`] assigned.
fn open_ty<'v>(env: &Env<'v>, c: &TyC<'v>, pending: u32) -> &'v TyClo<'v> {
    let want = glen(env) + pending;
    let mut clo = c.clo;
    let mut sat = c.sat;
    if sat < want {
        clo = weaken_ty_clo(clo, want - sat);
        sat = want;
    }
    let stop = sat.saturating_sub(pending).min(glen(env));
    if stop > c.home {
        let args: Vec<&'v TmClo<'v>> = (c.home..stop).map(|l| var_at(env, l)).collect();
        clo = apply_ty_clo(clo, &args);
    }
    clo
}

fn open_tm<'v>(env: &Env<'v>, c: &TmC<'v>, pending: u32) -> &'v TmClo<'v> {
    let want = glen(env) + pending;
    let mut clo = c.clo;
    let mut sat = c.sat;
    if sat < want {
        clo = weaken_tm_clo(clo, want - sat);
        sat = want;
    }
    let stop = sat.saturating_sub(pending).min(glen(env));
    if stop > c.home {
        let args: Vec<&'v TmClo<'v>> = (c.home..stop).map(|l| var_at(env, l)).collect();
        clo = apply_tm_clo(clo, &args);
    }
    clo
}

/// Run the machine on the checker's own budget. Fuel is a single shared
/// account (design §6): the evaluator spends from it and hands back what is
/// left, so a reduction step and a comparison node cost the same one unit
/// they cost today.
fn run<'v, T>(
    cv: &mut Conv<'v, Values>,
    env: &Env<'v>,
    f: impl FnOnce(&mut Eval<'_, 'v>) -> Result<T, crate::reduce::OutOfFuel>,
) -> R<T> {
    let defs = cv.defs(env);
    let mut ev = Eval::new(cv.fuel, defs, env.gamma.base, env.rho.arena());
    let out = f(&mut ev);
    cv.fuel = ev.fuel();
    out.map_err(|_| crate::conv::ConvError::OutOfFuel)
}

/// The definition at the head of a δ-stuck spine: at values it is one read,
/// because a glued neutral *is* the answer the syntactic `delta_head` walks a
/// spine to find (design §5).
fn glued<'v>(v: &Rc<Val<'v>>) -> Option<GlobalVar> {
    match &**v {
        Val::Neutral(n) if n.unfold.is_some() => match &n.head {
            Head::Global { var, .. } => Some(*var),
            _ => None,
        },
        _ => None,
    }
}

/// The neutral with its outermost elimination removed — an application's
/// function, an eliminator's scrutinee. The glued unfolding of the shorter
/// spine is recovered from the longer one's, which was built as exactly that
/// elimination applied to it.
fn spine_head<'v>(n: &Rc<VNeutral<'v>>) -> Rc<Val<'v>> {
    let mut spine = n.spine.clone();
    spine.pop();
    if spine.is_empty() {
        match &n.head {
            Head::BoxedGlobalTy(c) => return Rc::new(Val::BoxTy(Rc::clone(c))),
            Head::BoxedGlobalTm(c) => return Rc::new(Val::BoxTm(Rc::clone(c))),
            Head::Stuck(v) => return Rc::clone(v),
            _ => {}
        }
    }
    let unfold = match n.unfold {
        Some(TmClo::Elim { head, .. }) => Some(*head),
        _ => None,
    };
    Rc::new(Val::Neutral(Rc::new(VNeutral {
        head: n.head.clone(),
        spine,
        unfold,
    })))
}

thread_local! {
    /// The filler Γ entry: at the value domain nothing reads an entry's
    /// syntax (`Env<'v>::vtys` carries the domain object), only the length and
    /// the base.
    static FILLER: Rc<Type> = Rc::new(Type::Nat);
}

// ---------------------------------------------------------------------------
// The instantiation
// ---------------------------------------------------------------------------

impl<'v> Dom<'v> for Values {
    type Ty = Rc<VTy<'v>>;
    type Tm = Rc<Val<'v>>;
    type TyC = TyC<'v>;
    type TmC = TmC<'v>;
    type Subst = VSubst<'v>;
    type RecCtx = RecEnv<'v>;

    // -- reduction ----------------------------------------------------------

    fn whnf_ty(cv: &mut Conv<'v, Self>, env: &Env<'v>, t: &TyC<'v>) -> R<Rc<VTy<'v>>> {
        let c = open_ty(env, t, 0);
        run(cv, env, |ev| {
            let v = ev.force_ty(&c)?;
            ev.delta_whnf_ty(v)
        })
    }

    fn whnf_ty_root(cv: &mut Conv<'v, Self>, env: &Env<'v>, t: &Type) -> R<Rc<VTy<'v>>> {
        run(cv, env, |ev| ev.eval_ty(t, &env.rho))
    }

    fn whnf_tm_root(cv: &mut Conv<'v, Self>, env: &Env<'v>, t: &Term) -> R<Rc<Val<'v>>> {
        run(cv, env, |ev| ev.eval_tm_ref(t, &env.rho))
    }

    fn whnf_tm(cv: &mut Conv<'v, Self>, env: &Env<'v>, t: &TmC<'v>) -> R<Rc<Val<'v>>> {
        let c = open_tm(env, t, 0);
        run(cv, env, |ev| {
            let v = ev.force(&c)?;
            ev.delta_whnf(v)
        })
    }

    /// Forcing *is* the δ-opaque reduction: a definition becomes a glued
    /// neutral and its unfolding is a thunk nobody has pulled.
    fn whnf_ty_opaque(cv: &mut Conv<'v, Self>, env: &Env<'v>, t: &TyC<'v>) -> R<Rc<VTy<'v>>> {
        let c = open_ty(env, t, 0);
        run(cv, env, |ev| ev.force_ty(&c))
    }

    fn whnf_tm_opaque(cv: &mut Conv<'v, Self>, env: &Env<'v>, t: &TmC<'v>) -> R<Rc<Val<'v>>> {
        let c = open_tm(env, t, 0);
        run(cv, env, |ev| ev.force(&c))
    }

    fn delta_ty(cv: &mut Conv<'v, Self>, env: &Env<'v>, w: &Rc<VTy<'v>>) -> R<Rc<VTy<'v>>> {
        let w = Rc::clone(w);
        run(cv, env, |ev| ev.delta_step_ty(w))
    }

    fn delta_tm(cv: &mut Conv<'v, Self>, env: &Env<'v>, w: &Rc<Val<'v>>) -> R<Rc<Val<'v>>> {
        let w = Rc::clone(w);
        run(cv, env, |ev| ev.delta_step(w))
    }

    fn delta_head(_cv: &Conv<'v, Self>, _env: &Env<'v>, w: &Rc<Val<'v>>) -> Option<GlobalVar> {
        glued(w)
    }

    fn delta_head_ty(_cv: &Conv<'v, Self>, _env: &Env<'v>, w: &Rc<VTy<'v>>) -> Option<GlobalVar> {
        match &**w {
            VTy::Neutral(VNeTy::El { tm, .. }) => glued(tm),
            VTy::Vec { len, .. } | VTy::Fin { len } => glued(len),
            _ => None,
        }
    }

    /// The outermost elimination of the spine — a value's head is its *last*
    /// pushed elimination, where the syntax's is its outermost node.
    fn is_transp(w: &Rc<Val<'v>>) -> bool {
        matches!(&**w, Val::Neutral(n) if matches!(n.spine.last(), Some(Elim::Transp { .. })))
    }

    // -- views --------------------------------------------------------------

    fn view_ty<'a>(_cv: &mut Conv<'v, Self>, env: &Env<'v>, w: &'a Rc<VTy<'v>>) -> TyView<'a, 'v, Self> {
        match &**w {
            VTy::Nat => TyView::Nat,
            VTy::Ty(l) => TyView::Ty(l),
            VTy::Unit { level } => TyView::Unit { level },
            VTy::Empty { level } => TyView::Empty { level },
            VTy::SEmpty { level } => TyView::SEmpty { level },
            VTy::Squash { level, ty } => {
                TyView::Squash { level, ty: TyC::here(env, *ty) }
            }
            VTy::Pi { dom_level, cod_level, dom, cod } => TyView::Pi {
                dom_level,
                cod_level,
                dom: TyC::here(env, *dom),
                cod: TyC::under(env, *cod, 1),
            },
            VTy::Sigma { fst_level, snd_level, fst, snd } => TyView::Sigma {
                fst_level,
                snd_level,
                fst: TyC::here(env, *fst),
                snd: TyC::under(env, *snd, 1),
            },
            VTy::W { shape_level, pos_level, shape, pos } => TyView::W {
                shape_level,
                pos_level,
                shape: TyC::here(env, *shape),
                pos: TyC::under(env, *pos, 1),
            },
            VTy::Wf { level, shape, arity } => TyView::Wf {
                level,
                shape: TyC::here(env, *shape),
                arity: TmC::under(env, *arity, 1),
            },
            VTy::Sum { lhs_level, rhs_level, lhs, rhs } => TyView::Sum {
                lhs_level,
                rhs_level,
                lhs: TyC::here(env, *lhs),
                rhs: TyC::here(env, *rhs),
            },
            VTy::Id { level, ty, lhs, rhs } => TyView::Id {
                level,
                ty: TyC::here(env, *ty),
                lhs: TmC::here(env, *lhs),
                rhs: TmC::here(env, *rhs),
            },
            VTy::SEq { level, ty, lhs, rhs } => TyView::SEq {
                level,
                ty: TyC::here(env, *ty),
                lhs: TmC::here(env, *lhs),
                rhs: TmC::here(env, *rhs),
            },
            VTy::Vec { level, elem, len } => TyView::Vec {
                level,
                elem: TyC::here(env, *elem),
                len: TmC::value(env, Rc::clone(len)),
            },
            VTy::Fin { len } => TyView::Fin { len: TmC::value(env, Rc::clone(len)) },
            VTy::UPi { num_vars, level, body } => TyView::UPi {
                num_vars: *num_vars,
                level,
                body: TyC::here(env, *body),
            },
            VTy::CtxPi { level, body } => {
                TyView::CtxPi { level, body: TyC::here(env, *body) }
            }
            VTy::TyPi { ctx, arg_level, body_level, body } => TyView::TyPi {
                ctx,
                arg_level,
                body_level,
                body: TyC::here(env, *body),
            },
            VTy::CodeTy { ctx, level } => TyView::CodeTy { ctx, level },
            VTy::CodeTm { ctx, ty, level } => TyView::CodeTm { ctx, ty, level },
            VTy::Neutral(VNeTy::Global { var, subst }) => {
                TyView::GlobalTy { var: *var, subst }
            }
            VTy::Neutral(VNeTy::El { level, tm }) => {
                TyView::El { level, tm: TmC::value(env, Rc::clone(tm)) }
            }
        }
    }

    fn view_tm<'a>(_cv: &mut Conv<'v, Self>, env: &Env<'v>, w: &'a Rc<Val<'v>>) -> TmView<'a, 'v, Self> {
        match &**w {
            Val::TmNat => TmView::TmNat,
            Val::TmTy(l) => TmView::TmTy(l),
            Val::TmUnit { level } => TmView::TmUnit { level },
            Val::TmEmpty { level } => TmView::TmEmpty { level },
            Val::TmSEmpty { level } => TmView::TmSEmpty { level },
            Val::TmSquash { level, ty } => {
                TmView::TmSquash { level, ty: TmC::here(env, *ty) }
            }
            Val::TmPi { dom_level, cod_level, dom, cod } => TmView::TmPi {
                dom_level,
                cod_level,
                dom: TmC::here(env, *dom),
                cod: TmC::under(env, *cod, 1),
            },
            Val::TmSigma { fst_level, snd_level, fst, snd } => TmView::TmSigma {
                fst_level,
                snd_level,
                fst: TmC::here(env, *fst),
                snd: TmC::under(env, *snd, 1),
            },
            Val::TmW { shape_level, pos_level, shape, pos } => TmView::TmW {
                shape_level,
                pos_level,
                shape: TmC::here(env, *shape),
                pos: TmC::under(env, *pos, 1),
            },
            Val::TmWf { level, shape, arity } => TmView::TmWf {
                level,
                shape: TmC::here(env, *shape),
                arity: TmC::under(env, *arity, 1),
            },
            Val::TmId { level, ty, lhs, rhs } => TmView::TmId {
                level,
                ty: TmC::here(env, *ty),
                lhs: TmC::here(env, *lhs),
                rhs: TmC::here(env, *rhs),
            },
            Val::TmSEq { level, ty, lhs, rhs } => TmView::TmSEq {
                level,
                ty: TmC::here(env, *ty),
                lhs: TmC::here(env, *lhs),
                rhs: TmC::here(env, *rhs),
            },
            Val::TmSum { lhs_level, rhs_level, lhs, rhs } => TmView::TmSum {
                lhs_level,
                rhs_level,
                lhs: TmC::here(env, *lhs),
                rhs: TmC::here(env, *rhs),
            },
            Val::TmVec { level, elem, len } => TmView::TmVec {
                level,
                elem: TmC::here(env, *elem),
                len: TmC::here(env, *len),
            },
            Val::TmFin { len } => TmView::TmFin { len: TmC::here(env, *len) },

            Val::Zero => TmView::Zero,
            Val::Succ(t) => TmView::Succ(TmC::here(env, *t)),
            Val::NatRun { program, tail } => TmView::Succ(TmC::here(
                env,
                Val::nat_run_pred(env.rho.arena(), program, tail),
            )),
            Val::Refl { tm, .. } => TmView::Refl { tm: TmC::here(env, *tm) },
            Val::Inl { val, .. } => TmView::Inl { val: TmC::here(env, *val) },
            Val::Inr { val, .. } => TmView::Inr { val: TmC::here(env, *val) },
            Val::Sup { label, children, .. } => TmView::Sup {
                label: TmC::here(env, *label),
                children: TmC::here(env, *children),
            },
            Val::Supf { label, children, .. } => TmView::Supf {
                label: TmC::here(env, *label),
                children: TmC::here(env, *children),
            },
            Val::BoxTy(t) => TmView::BoxTy(t),
            Val::BoxTm(t) => TmView::BoxTm(t),

            Val::Lam { .. }
            | Val::NatSync { .. }
            | Val::ULam { .. }
            | Val::CtxLam { .. }
            | Val::TyLam { .. }
            | Val::Pair { .. }
            | Val::Triv { .. }
            | Val::SRefl { .. }
            | Val::Squash { .. } => TmView::Opaque,

            Val::Neutral(n) => view_neutral(env, n),
        }
    }

    fn head_tm(cv: &mut Conv<'v, Self>, env: &Env<'v>, t: &TmC<'v>) -> R<Rc<Val<'v>>> {
        let c = open_tm(env, t, 0);
        run(cv, env, |ev| ev.force(&c))
    }

    fn as_child_ty(_cv: &mut Conv<'v, Self>, env: &Env<'v>, w: &Rc<VTy<'v>>) -> R<TyC<'v>> {
        Ok(TyC::value(env, Rc::clone(w)))
    }

    // -- scope --------------------------------------------------------------

    fn push_entry(env: &Env<'v>, ty: &TyC<'v>, level: &Level) -> Env<'v> {
        let vty = open_ty(env, ty, 0);
        env.push_entry(FILLER.with(Rc::clone), vty, level.clone())
    }

    fn push_spec(env: &Env<'v>, tele: &rec::Tele) -> Env<'v> {
        let mut e = env.push_tele(tele.univs, tele.globals.clone());
        for (ty, level) in &tele.locals {
            let vty = e.rho.arena().ty(TyClo::new(e.rho, Rc::clone(ty)));
            e = e.push_entry(Rc::clone(ty), vty, level.clone());
        }
        e.tele.2 = tele.locals.len() as u32;
        e
    }

    /// The type of a local, from the domain-object list Γ is carried
    /// alongside for. Weakening it into the variable's own scope is nothing:
    /// a value's variables are levels.
    ///
    /// A variable of the **abstract prefix** has no type here, exactly as it
    /// has none at the syntax domain, and both answer `NotConvertible`.
    fn var_type(_cv: &mut Conv<'v, Self>, env: &Env<'v>, x: LocalVar) -> R<(TyC<'v>, Level)> {
        // Conversion's own binders carry their type as a domain object;
        // everything older is still syntax in Γ, read in the identity
        // environment of the prefix it is scoped in.
        let n = glen(env);
        let Some(i) = n.checked_sub(1 + x.0) else {
            return Err(NC);
        };
        if i >= env.vbase {
            let Some((clo, level)) = env.vtys.nth(x.0) else {
                return Err(NC);
            };
            return Ok((TyC::here(env, clo), level.clone()));
        }
        let Some(e) = env.gamma.entries.nth_inner(x.0) else {
            return Err(NC);
        };
        let rho = value::Env::identity(env.rho.arena(), i);
        let clo = env.rho.arena().ty(TyClo::new(rho, Rc::clone(&e.ty)));
        Ok((TyC::here(env, clo), e.level.clone()))
    }

    fn weaken_ty(t: &TyC<'v>, by: u32) -> TyC<'v> {
        TyC {
            clo: weaken_ty_clo(t.clo, by),
            home: t.home,
            sat: t.sat + by,
        }
    }

    fn weaken_tm(t: &TmC<'v>, by: u32) -> TmC<'v> {
        TmC {
            clo: weaken_tm_clo(t.clo, by),
            home: t.home,
            sat: t.sat + by,
        }
    }

    // -- embedding ----------------------------------------------------------

    fn embed_ty(env: &Env<'v>, t: Rc<Type>) -> TyC<'v> {
        TyC::here(env, env.rho.arena().ty(TyClo::new(env.rho, t)))
    }

    /// Raw syntax scoped in Γ-plus-telescope, read in the recursor's own
    /// environment: the stored environment is carried across the telescope
    /// [`Dom::push_spec`] just pushed — weakened in the outer namespaces,
    /// extended by the telescope's local binders.
    fn embed_ty_at(rec: &RecEnv<'v>, env: &Env<'v>, t: Rc<Type>) -> TyC<'v> {
        TyC::here(env, env.rho.arena().ty(TyClo::new(rec_env(rec, env), t)))
    }

    fn embed_tm_at(rec: &RecEnv<'v>, env: &Env<'v>, t: Rc<Term>) -> TmC<'v> {
        TmC::here(env, env.rho.arena().tm(TmClo::syn(rec_env(rec, env), t)))
    }

    // -- instantiation ------------------------------------------------------

    /// Closure application, which is why this could not stay at the call
    /// sites: the identity substitution the syntax domain builds is exactly
    /// the environment the closure already has.
    fn inst_ty(
        _cv: &mut Conv<'v, Self>,
        home: &Env<'v>,
        cur: &Env<'v>,
        m: &TyC<'v>,
        args: &[TmC<'v>],
    ) -> R<TyC<'v>> {
        let k = args.len() as u32;
        let clo = open_ty(home, m, k);
        let vals: Vec<&'v TmClo<'v>> = args.iter().map(|a| open_tm(cur, a, 0)).collect();
        Ok(TyC::here(cur, apply_ty_clo(&clo, &vals)))
    }

    fn inst_tm(
        _cv: &mut Conv<'v, Self>,
        home: &Env<'v>,
        cur: &Env<'v>,
        m: &TmC<'v>,
        args: &[TmC<'v>],
    ) -> R<TmC<'v>> {
        let k = args.len() as u32;
        let clo = open_tm(home, m, k);
        let vals: Vec<&'v TmClo<'v>> = args.iter().map(|a| open_tm(cur, a, 0)).collect();
        Ok(TmC::here(cur, apply_tm_clo(&clo, &vals)))
    }

    fn shift_global_ty(_cv: &mut Conv<'v, Self>, env: &Env<'v>, t: &TyC<'v>, by: u32) -> R<TyC<'v>> {
        let o = Outer { arena: env.rho.arena(), univs: 0, globals: by };
        Ok(TyC { clo: value::shift::ty_clo(t.clo, o), home: t.home, sat: t.sat })
    }

    /// Instantiating a `ΠΠ` binder leaves the captured environment alone:
    /// `inst_univ` renumbers the outer scope back *down*, so the environment
    /// is already in the post-instantiation scope (stage 1's log, note 4).
    fn inst_univ_ty(_cv: &mut Conv<'v, Self>, env: &Env<'v>, body: &TyC<'v>, phi: &[Level]) -> R<TyC<'v>> {
        let Some((benv, bbody)) = body.clo.as_syn() else {
            return Err(NC);
        };
        Ok(TyC::here(
            env,
            env.rho.arena().ty(TyClo::new(*benv, Rc::new(bbody.inst_univ(phi)))),
        ))
    }

    fn inst_ctx_ty(_cv: &mut Conv<'v, Self>, env: &Env<'v>, body: &TyC<'v>, ctx: &LocalCtx) -> R<TyC<'v>> {
        inst_global_ty(env, body, GlobalSubst::single(GlobalEntry::Ctx(ctx.clone())))
    }

    fn inst_tyarg_ty(_cv: &mut Conv<'v, Self>, env: &Env<'v>, body: &TyC<'v>, arg: &Rc<Type>) -> R<TyC<'v>> {
        inst_global_ty(env, body, GlobalSubst::single(GlobalEntry::Ty(Rc::clone(arg))))
    }

    fn under_tele_ty(_cv: &mut Conv<'v, Self>, env: &Env<'v>, t: &TyC<'v>, tu: u32, tg: u32) -> R<TyC<'v>> {
        let o = Outer { arena: env.rho.arena(), univs: tu, globals: tg };
        Ok(TyC { clo: value::shift::reenv_ty(t.clo, o), home: t.home, sat: t.sat })
    }

    fn under_tele_tm(_cv: &mut Conv<'v, Self>, env: &Env<'v>, t: &TmC<'v>, tu: u32, tg: u32) -> R<TmC<'v>> {
        let o = Outer { arena: env.rho.arena(), univs: tu, globals: tg };
        Ok(TmC { clo: value::shift::reenv_tm(t.clo, o), home: t.home, sat: t.sat })
    }

    // -- local substitutions ------------------------------------------------

    fn subst_len(d: &VSubst<'v>) -> usize {
        d.terms.len()
    }

    fn subst_term(env: &Env<'v>, d: &VSubst<'v>, k: usize) -> TmC<'v> {
        TmC::value(env, Rc::clone(&d.terms[k]))
    }

    /// `VTail`'s coarser test: the source context's length and `·`'s base are
    /// dropped, because an environment machine — having substituted nothing —
    /// never renormalizes them, and both are determined by the scope, which
    /// the two sides of a comparison share (stage 1's log, note 2).
    fn subst_tails_agree(a: &VSubst<'v>, b: &VSubst<'v>) -> bool {
        a.tail == b.tail
    }

    /// `T[δ|ₖ]` — the target-context entry type read under the first `k`
    /// payloads. Those payloads are already values; past them the lookup
    /// falls through to the abstract prefix either way (`eval.rs`'s note on
    /// `global_tm`).
    fn apply_subst_ty(
        _cv: &mut Conv<'v, Self>,
        env: &Env<'v>,
        d: &VSubst<'v>,
        k: usize,
        t: &Rc<Type>,
    ) -> R<TyC<'v>> {
        let mut e = value::Env::empty(env.rho.arena());
        for v in &d.terms[..k] {
            e = e.push(env.rho.arena().tm(TmClo::val(Rc::clone(v))));
        }
        Ok(TyC::here(env, env.rho.arena().ty(TyClo::new(e, Rc::clone(t)))))
    }

    // -- synthesized types --------------------------------------------------

    fn nat(env: &Env<'v>) -> TyC<'v> {
        TyC::value(env, Rc::new(VTy::Nat))
    }

    fn univ(env: &Env<'v>, level: &Level) -> TyC<'v> {
        TyC::value(env, Rc::new(VTy::Ty(level.clone())))
    }

    fn empty(env: &Env<'v>, level: &Level) -> TyC<'v> {
        TyC::value(env, Rc::new(VTy::Empty { level: level.clone() }))
    }

    fn sempty(env: &Env<'v>, level: &Level) -> TyC<'v> {
        TyC::value(env, Rc::new(VTy::SEmpty { level: level.clone() }))
    }

    fn squash(env: &Env<'v>, level: &Level, ty: &TyC<'v>) -> TyC<'v> {
        TyC::value(
            env,
            Rc::new(VTy::Squash { level: level.clone(), ty: ty.clo }),
        )
    }

    fn code_ty(env: &Env<'v>, ctx: &LocalCtx, level: &Level) -> TyC<'v> {
        TyC::value(
            env,
            Rc::new(VTy::CodeTy { ctx: ctx.clone(), level: level.clone() }),
        )
    }

    fn code_tm(env: &Env<'v>, ctx: &LocalCtx, ty: &Rc<Type>, level: &Level) -> TyC<'v> {
        TyC::value(
            env,
            Rc::new(VTy::CodeTm {
                ctx: ctx.clone(),
                ty: Rc::clone(ty),
                level: level.clone(),
            }),
        )
    }

    /// `El` is a redex-or-neutral and has no canonical value, so this is the
    /// domain's own lazy `El` — built, like the syntax domain's, without
    /// reducing anything.
    fn el(_cv: &mut Conv<'v, Self>, env: &Env<'v>, level: &Level, tm: &TmC<'v>) -> R<TyC<'v>> {
        let c = open_tm(env, tm, 0);
        Ok(TyC::here(env, env.rho.arena().ty(TyClo::el(level.clone(), c))))
    }

    fn pi(
        _cv: &mut Conv<'v, Self>,
        env: &Env<'v>,
        dom_level: &Level,
        cod_level: &Level,
        dom: &TyC<'v>,
        cod: &TyC<'v>,
    ) -> R<TyC<'v>> {
        Ok(TyC::value(
            env,
            Rc::new(VTy::Pi {
                dom_level: dom_level.clone(),
                cod_level: cod_level.clone(),
                dom: open_ty(env, dom, 0),
                cod: open_ty(env, cod, 1),
            }),
        ))
    }

    fn sum(
        _cv: &mut Conv<'v, Self>,
        env: &Env<'v>,
        lhs_level: &Level,
        rhs_level: &Level,
        lhs: &TyC<'v>,
        rhs: &TyC<'v>,
    ) -> R<TyC<'v>> {
        Ok(TyC::value(
            env,
            Rc::new(VTy::Sum {
                lhs_level: lhs_level.clone(),
                rhs_level: rhs_level.clone(),
                lhs: open_ty(env, lhs, 0),
                rhs: open_ty(env, rhs, 0),
            }),
        ))
    }

    fn w(
        _cv: &mut Conv<'v, Self>,
        env: &Env<'v>,
        shape_level: &Level,
        pos_level: &Level,
        shape: &TyC<'v>,
        pos: &TyC<'v>,
    ) -> R<TyC<'v>> {
        Ok(TyC::value(
            env,
            Rc::new(VTy::W {
                shape_level: shape_level.clone(),
                pos_level: pos_level.clone(),
                shape: open_ty(env, shape, 0),
                pos: open_ty(env, pos, 1),
            }),
        ))
    }

    fn wf(
        _cv: &mut Conv<'v, Self>,
        env: &Env<'v>,
        level: &Level,
        shape: &TyC<'v>,
        arity: &TmC<'v>,
    ) -> R<TyC<'v>> {
        Ok(TyC::value(
            env,
            Rc::new(VTy::Wf {
                level: level.clone(),
                shape: open_ty(env, shape, 0),
                arity: open_tm(env, arity, 1),
            }),
        ))
    }

    /// Held unforced, like the syntax domain's `Type::Vec`: at a canonical
    /// length it steps, and whoever whnfs it pays for that.
    fn vec(
        _cv: &mut Conv<'v, Self>,
        env: &Env<'v>,
        level: &Level,
        elem: &TyC<'v>,
        len: &TmC<'v>,
    ) -> R<TyC<'v>> {
        Ok(TyC::here(
            env,
            env.rho.arena().ty(TyClo::vec(
                level.clone(),
                open_ty(env, elem, 0),
                open_tm(env, len, 0),
            )),
        ))
    }

    fn id(
        _cv: &mut Conv<'v, Self>,
        env: &Env<'v>,
        level: &Level,
        ty: &TyC<'v>,
        lhs: &TmC<'v>,
        rhs: &TmC<'v>,
    ) -> R<TyC<'v>> {
        Ok(TyC::value(
            env,
            Rc::new(VTy::Id {
                level: level.clone(),
                ty: open_ty(env, ty, 0),
                lhs: open_tm(env, lhs, 0),
                rhs: open_tm(env, rhs, 0),
            }),
        ))
    }

    // -- synthesized terms --------------------------------------------------

    fn zero(env: &Env<'v>) -> TmC<'v> {
        TmC::value(env, Rc::new(Val::Zero))
    }

    fn succ(_cv: &mut Conv<'v, Self>, env: &Env<'v>, t: &TmC<'v>) -> R<TmC<'v>> {
        Ok(TmC::value(
            env,
            Rc::new(Val::Succ(open_tm(env, t, 0))),
        ))
    }

    fn local(env: &Env<'v>, x: LocalVar) -> TmC<'v> {
        let n = glen(env);
        let v = match n.checked_sub(1 + x.0) {
            Some(level) => Val::var(level),
            None => Val::base_var(x.0 - n),
        };
        TmC::value(env, Rc::new(v))
    }

    fn refl(
        _cv: &mut Conv<'v, Self>,
        env: &Env<'v>,
        level: &Level,
        ty: &TyC<'v>,
        tm: &TmC<'v>,
    ) -> R<TmC<'v>> {
        Ok(TmC::value(
            env,
            Rc::new(Val::Refl {
                level: level.clone(),
                ty: open_ty(env, ty, 0),
                tm: open_tm(env, tm, 0),
            }),
        ))
    }

    fn inj(
        _cv: &mut Conv<'v, Self>,
        env: &Env<'v>,
        left: bool,
        lhs_level: &Level,
        rhs_level: &Level,
        lhs: &TyC<'v>,
        rhs: &TyC<'v>,
        val: &TmC<'v>,
    ) -> R<TmC<'v>> {
        let (ll, rl) = (lhs_level.clone(), rhs_level.clone());
        let (l, r) = (open_ty(env, lhs, 0), open_ty(env, rhs, 0));
        let v = open_tm(env, val, 0);
        Ok(TmC::value(
            env,
            Rc::new(if left {
                Val::Inl { lhs_level: ll, rhs_level: rl, lhs: l, rhs: r, val: v }
            } else {
                Val::Inr { lhs_level: ll, rhs_level: rl, lhs: l, rhs: r, val: v }
            }),
        ))
    }

    /// The `W` annotations come from the type, as the rule itself takes them;
    /// `by` is nothing here, since weakening is nothing here.
    fn sup_at(
        cv: &mut Conv<'v, Self>,
        env: &Env<'v>,
        w: &TyC<'v>,
        _by: u32,
        label: &TmC<'v>,
        children: &TmC<'v>,
    ) -> R<TmC<'v>> {
        let wv = Self::whnf_ty(cv, env, w)?;
        let VTy::W { shape_level, pos_level, shape, pos } = &*wv else {
            return Err(NC);
        };
        Ok(TmC::value(
            env,
            Rc::new(Val::Sup {
                shape_level: shape_level.clone(),
                pos_level: pos_level.clone(),
                shape_ty: *shape,
                pos_ty: *pos,
                label: open_tm(env, label, 0),
                children: open_tm(env, children, 0),
            }),
        ))
    }

    /// Scoped identity: `false` is always safe. Two sub-structures that are
    /// the same object — or syntactic closures over the *same* environment
    /// with α-equal bodies (evaluation is a function of the pair) — are
    /// definitionally the same type.
    fn ty_eq_fast(a: &TyC<'v>, b: &TyC<'v>) -> bool {
        a.home == b.home
            && a.sat == b.sat
            && (std::ptr::eq(a.clo, b.clo)
                || match (a.clo.as_syn(), b.clo.as_syn()) {
                    (Some((e1, b1)), Some((e2, b2))) => {
                        value::Env::ptr_eq(e1, e2) && (Rc::ptr_eq(b1, b2) || b1 == b2)
                    }
                    _ => false,
                })
    }

    fn app_annotation_fast(env: &Env<'v>, a: &TyC<'v>, b: &TyC<'v>, codomain: bool) -> bool {
        let ordinary = Self::ty_eq_fast(a, b);
        let env_hit = !ordinary
            && a.home == b.home
            && a.sat == b.sat
            && matches!(
                (a.clo.as_syn(), b.clo.as_syn()),
                (Some((e1, b1)), Some((e2, b2)))
                    if Rc::ptr_eq(b1, b2) && value::Env::values_ptr_eq(e1, e2)
            );
        let fast = ordinary || env_hit;
        env.rho.arena().record_app_annotation(codomain, fast, env_hit);
        fast
    }

    /// Scoped identity ([`Values::ty_eq_fast`]) for terms: one closure — or
    /// one (environment, body) denotation — opened with the same pending
    /// binders denotes the same term on both sides.
    fn tm_identity_fast(a: &TmC<'v>, b: &TmC<'v>) -> bool {
        a.home == b.home
            && a.sat == b.sat
            && (std::ptr::eq(a.clo, b.clo)
                || match (a.clo.as_syn(), b.clo.as_syn()) {
                    (Some((e1, b1)), Some((e2, b2))) => {
                        value::Env::ptr_eq(e1, e2) && (Rc::ptr_eq(b1, b2) || b1 == b2)
                    }
                    _ => false,
                })
    }

    /// The same scoped identity is also the commonest endpoint equality the
    /// strip loop meets.
    fn tm_eq_fast(a: &TmC<'v>, b: &TmC<'v>) -> bool {
        Self::tm_identity_fast(a, b)
            || a.home == b.home
                && a.sat == b.sat
                && matches!(
                    (a.clo, b.clo),
                    (
                        TmClo::Val(left),
                        TmClo::Val(right),
                    ) if matches!(
                        (&**left, &**right),
                        (
                            Val::NatRun { program: p1, tail: t1 },
                            Val::NatRun { program: p2, tail: t2 },
                        ) if value::program::ContextProgram::equivalent_fast(p1, p2)
                            && (std::ptr::eq(*t1, *t2)
                                || matches!(
                                    (t1.as_syn(), t2.as_syn()),
                                    (Some((e1, b1)), Some((e2, b2)))
                                        if value::Env::ptr_eq(e1, e2)
                                            && (Rc::ptr_eq(b1, b2) || b1 == b2)
                                ))
                    )
                )
    }

    fn cancel_nat_prefix(
        cv: &mut Conv<'v, Self>,
        env: &Env<'v>,
        a: &Rc<Val<'v>>,
        b: &Rc<Val<'v>>,
    ) -> R<Option<(TmC<'v>, TmC<'v>)>> {
        let (
            Val::NatRun { program: left, tail: left_tail },
            Val::NatRun { program: right, tail: right_tail },
        ) = (&**a, &**b)
        else {
            return Ok(None);
        };
        let cancelled = value::program::ContextProgram::cancel_matching_prefix(
            Rc::clone(left),
            Rc::clone(right),
            cv.fuel,
        )
        .map_err(|_| {
            cv.fuel = 0;
            crate::conv::ConvError::OutOfFuel
        })?;
        cv.fuel -= cancelled.inspected;
        if !cancelled.changed {
            return Ok(None);
        }
        let arena = env.rho.arena();
        let residual = |program, tail| match program {
            None => tail,
            Some(program) => arena.tm(TmClo::val(Rc::new(Val::NatRun { program, tail }))),
        };
        Ok(Some((
            TmC::here(env, residual(cancelled.left, left_tail)),
            TmC::here(env, residual(cancelled.right, right_tail)),
        )))
    }

    fn app(
        cv: &mut Conv<'v, Self>,
        env: &Env<'v>,
        dom_level: &Level,
        cod_level: &Level,
        dom: &TyC<'v>,
        cod: &TyC<'v>,
        fun: &TmC<'v>,
        arg: &TmC<'v>,
    ) -> R<TmC<'v>> {
        let e = Elim::App {
            dom_level: dom_level.clone(),
            cod_level: cod_level.clone(),
            dom: open_ty(env, dom, 0),
            cod: open_ty(env, cod, 1),
            arg: open_tm(env, arg, 0),
        };
        let f = open_tm(env, fun, 0);
        let v = run(cv, env, |ev| {
            let f = ev.force(&f)?;
            ev.elim(f, e)
        })?;
        Ok(TmC::value(env, v))
    }

    fn proj(
        cv: &mut Conv<'v, Self>,
        env: &Env<'v>,
        first: bool,
        fst_level: &Level,
        snd_level: &Level,
        fst_ty: &TyC<'v>,
        snd_ty: &TyC<'v>,
        pair: &TmC<'v>,
    ) -> R<TmC<'v>> {
        let e = proj_elim(env, first, fst_level, snd_level, fst_ty, snd_ty);
        let p = open_tm(env, pair, 0);
        let v = run(cv, env, |ev| {
            let p = ev.force(&p)?;
            ev.elim(p, e)
        })?;
        Ok(TmC::value(env, v))
    }

    fn box_ty(env: &Env<'v>, code: Rc<Type>) -> TmC<'v> {
        TmC::value(env, Rc::new(Val::BoxTy(code)))
    }

    fn box_tm(env: &Env<'v>, code: Rc<Term>) -> TmC<'v> {
        TmC::value(env, Rc::new(Val::BoxTm(code)))
    }

    fn box_ty_payload(cv: &mut Conv<'v, Self>, env: &Env<'v>, t: &TmC<'v>) -> R<Option<Rc<Type>>> {
        let v = Self::head_tm(cv, env, t)?;
        Ok(match &*v {
            Val::BoxTy(c) => Some(Rc::clone(c)),
            _ => None,
        })
    }

    fn box_tm_payload(cv: &mut Conv<'v, Self>, env: &Env<'v>, t: &TmC<'v>) -> R<Option<Rc<Term>>> {
        let v = Self::head_tm(cv, env, t)?;
        Ok(match &*v {
            Val::BoxTm(c) => Some(Rc::clone(c)),
            _ => None,
        })
    }

    // -- η -----------------------------------------------------------------

    /// Closure application, not syntax: the shift dance the syntax domain
    /// performs to build `w↑ x` is the operation this domain does not have.
    fn eta_app(
        cv: &mut Conv<'v, Self>,
        outer: &Env<'v>,
        inner: &Env<'v>,
        a: &Rc<Val<'v>>,
        b: &Rc<Val<'v>>,
        dom_level: &Level,
        cod_level: &Level,
        dom: &TyC<'v>,
        cod: &TyC<'v>,
    ) -> R<(TmC<'v>, TmC<'v>)> {
        let e = Elim::App {
            dom_level: dom_level.clone(),
            cod_level: cod_level.clone(),
            dom: open_ty(outer, dom, 0),
            cod: open_ty(outer, cod, 1),
            arg: var_at(inner, glen(outer)),
        };
        let (a, b) = (Rc::clone(a), Rc::clone(b));
        let (x, y) = run(cv, inner, |ev| {
            let x = ev.elim(a, e.clone())?;
            let y = ev.elim(b, e)?;
            Ok((x, y))
        })?;
        Ok((TmC::value(inner, x), TmC::value(inner, y)))
    }

    fn eta_uapp(
        cv: &mut Conv<'v, Self>,
        _outer: &Env<'v>,
        inner: &Env<'v>,
        a: &Rc<Val<'v>>,
        b: &Rc<Val<'v>>,
        num_vars: u32,
    ) -> R<(TmC<'v>, TmC<'v>)> {
        let o = Outer { arena: inner.rho.arena(), univs: num_vars, globals: 0 };
        let (a, b) = (value::shift::val(a, o), value::shift::val(b, o));
        let levels: Vec<Level> = (0..num_vars).rev().map(rec::lvar).collect();
        let e = Elim::UApp { levels };
        let (x, y) = run(cv, inner, |ev| {
            let x = ev.elim(a, e.clone())?;
            let y = ev.elim(b, e)?;
            Ok((x, y))
        })?;
        Ok((TmC::value(inner, x), TmC::value(inner, y)))
    }

    fn eta_ctxapp(
        cv: &mut Conv<'v, Self>,
        _outer: &Env<'v>,
        inner: &Env<'v>,
        a: &Rc<Val<'v>>,
        b: &Rc<Val<'v>>,
    ) -> R<(TmC<'v>, TmC<'v>)> {
        let o = Outer { arena: inner.rho.arena(), univs: 0, globals: 1 };
        let (a, b) = (value::shift::val(a, o), value::shift::val(b, o));
        let e = Elim::CtxApp { ctx: rec::g_ctx(0) };
        let (x, y) = run(cv, inner, |ev| {
            let x = ev.elim(a, e.clone())?;
            let y = ev.elim(b, e)?;
            Ok((x, y))
        })?;
        Ok((TmC::value(inner, x), TmC::value(inner, y)))
    }

    fn eta_tyapp(
        cv: &mut Conv<'v, Self>,
        _outer: &Env<'v>,
        inner: &Env<'v>,
        a: &Rc<Val<'v>>,
        b: &Rc<Val<'v>>,
        ctx: &LocalCtx,
    ) -> R<(TmC<'v>, TmC<'v>)> {
        let o = Outer { arena: inner.rho.arena(), univs: 0, globals: 1 };
        let (a, b) = (value::shift::val(a, o), value::shift::val(b, o));
        let e = Elim::TyApp { arg: Rc::new(rec::gty(0, &ctx.shift_global(1))) };
        let (x, y) = run(cv, inner, |ev| {
            let x = ev.elim(a, e.clone())?;
            let y = ev.elim(b, e)?;
            Ok((x, y))
        })?;
        Ok((TmC::value(inner, x), TmC::value(inner, y)))
    }

    fn eta_proj(
        cv: &mut Conv<'v, Self>,
        env: &Env<'v>,
        first: bool,
        a: &Rc<Val<'v>>,
        b: &Rc<Val<'v>>,
        fst_level: &Level,
        snd_level: &Level,
        fst_ty: &TyC<'v>,
        snd_ty: &TyC<'v>,
    ) -> R<(TmC<'v>, TmC<'v>)> {
        let e = proj_elim(env, first, fst_level, snd_level, fst_ty, snd_ty);
        let (a, b) = (Rc::clone(a), Rc::clone(b));
        let (x, y) = run(cv, env, |ev| {
            let x = ev.elim(a, e.clone())?;
            let y = ev.elim(b, e)?;
            Ok((x, y))
        })?;
        Ok((TmC::value(env, x), TmC::value(env, y)))
    }

    // -- recursors ----------------------------------------------------------

    /// ch. 04's `(cs, ih, s)`, from the **shared** schema. The closures'
    /// syntax and their common environment are taken apart, the schema builds
    /// three types in that environment's scope plus the three binders
    /// conversion is about to push, and each is embedded with exactly those
    /// binders' neutrals. Rebuilding `nth` out of domain constructors would
    /// need a native closure and a seventh transcription; this needs neither.
    fn wf_step_telescope(
        _cv: &mut Conv<'v, Self>,
        env: &Env<'v>,
        level: &Level,
        motive_level: &Level,
        shape: &TyC<'v>,
        arity: &TmC<'v>,
        motive: &TyC<'v>,
    ) -> R<(TyC<'v>, TyC<'v>, TyC<'v>)> {
        let (Some((senv, sbody)), Some((aenv, abody)), Some((menv, mbody))) = (
            shape.clo.as_syn(),
            arity.clo.as_syn(),
            motive.clo.as_syn(),
        ) else {
            return Err(NC);
        };
        if senv.len() != aenv.len() || senv.len() != menv.len() {
            return Err(NC);
        }
        let gamma = LocalCtx {
            base: env.gamma.base,
            entries: CtxEntries::repeat(
                CtxEntry { ty: FILLER.with(Rc::clone), level: Level::Zero },
                senv.len() as usize,
            ),
        };
        let (cs, ih, step) =
            wf_step_telescope(&gamma, level, motive_level, sbody, abody, mbody);
        let l = glen(env);
        let e1 = senv.push(fresh(&senv, l));
        let e2 = e1.push(fresh(&e1, l + 1));
        let e3 = e2.push(fresh(&e2, l + 2));
        Ok((
            TyC { clo: env.rho.arena().ty(TyClo::new(e1, Rc::new(cs))), home: l + 1, sat: l + 1 },
            TyC { clo: env.rho.arena().ty(TyClo::new(e2, Rc::new(ih))), home: l + 2, sat: l + 2 },
            TyC { clo: env.rho.arena().ty(TyClo::new(e3, Rc::new(step))), home: l + 3, sat: l + 3 },
        ))
    }

    /// `M_Typ[l/ℓ, Δ/g, t/x_T]`. The universe and global halves are syntactic
    /// (design §3.1); the local half — `M[…]` at the scrutinee under `id_Γ` —
    /// is one environment cell.
    fn inst_ty_motive(
        _cv: &mut Conv<'v, Self>,
        env: &Env<'v>,
        rec: &RecEnv<'v>,
        motive: &Rc<Type>,
        code_level: &Level,
        ctx: &LocalCtx,
        scrut: &TmC<'v>,
    ) -> R<TyC<'v>> {
        let body = motive
            .inst_univ(&[code_level.clone()])
            .apply_global(&GlobalSubst::single(GlobalEntry::Ctx(ctx.clone())));
        let e = rec.0.push(open_tm(env, scrut, 0));
        Ok(TyC::here(env, env.rho.arena().ty(TyClo::new(e, Rc::new(body)))))
    }

    fn inst_tm_motive(
        _cv: &mut Conv<'v, Self>,
        env: &Env<'v>,
        rec: &RecEnv<'v>,
        motive: &Rc<Type>,
        code_level: &Level,
        ctx: &LocalCtx,
        ty: &Rc<Type>,
        scrut: &TmC<'v>,
    ) -> R<TyC<'v>> {
        let body = motive.inst_univ(&[code_level.clone()]).apply_global(&GlobalSubst {
            entries: vec![
                GlobalEntry::Ctx(ctx.clone()),
                GlobalEntry::Ty(Rc::clone(ty)),
            ],
        });
        let e = rec.0.push(open_tm(env, scrut, 0));
        Ok(TyC::here(env, env.rho.arena().ty(TyClo::new(e, Rc::new(body)))))
    }
}

// ---------------------------------------------------------------------------
// Helpers the impl shares
// ---------------------------------------------------------------------------

fn inst_global_ty<'v>(env: &Env<'v>, body: &TyC<'v>, sigma: GlobalSubst) -> R<TyC<'v>> {
    let Some((benv, bbody)) = body.clo.as_syn() else {
        return Err(NC);
    };
    Ok(TyC::here(
        env,
        env.rho.arena().ty(TyClo::new(*benv, Rc::new(bbody.apply_global(&sigma)))),
    ))
}

fn proj_elim<'v>(
    env: &Env<'v>,
    first: bool,
    fst_level: &Level,
    snd_level: &Level,
    fst_ty: &TyC<'v>,
    snd_ty: &TyC<'v>,
) -> Elim<'v> {
    let (fl, sl) = (fst_level.clone(), snd_level.clone());
    let (ft, st) = (open_ty(env, fst_ty, 0), open_ty(env, snd_ty, 1));
    if first {
        Elim::Fst { fst_level: fl, snd_level: sl, fst_ty: ft, snd_ty: st }
    } else {
        Elim::Snd { fst_level: fl, snd_level: sl, fst_ty: ft, snd_ty: st }
    }
}

/// The environment a recursor's Γ-scoped syntax is read in, carried across
/// the telescope [`Dom::push_spec`] pushed.
fn rec_env<'v>(rec: &RecEnv<'v>, env: &Env<'v>) -> value::Env<'v> {
    let (tu, tg, tl) = env.tele;
    let mut e = value::shift::env(
        &rec.0,
        Outer { arena: env.rho.arena(), univs: tu, globals: tg },
    );
    let base = glen(env) - tl;
    for i in 0..tl {
        e = e.push(fresh(&e, base + i));
    }
    e
}

/// A neutral's view: its outermost elimination, with the shorter spine as the
/// function or scrutinee. The empty spine is the head itself.
fn view_neutral<'a, 'v>(env: &Env<'v>, n: &'a Rc<VNeutral<'v>>) -> TmView<'a, 'v, Values> {
    let Some(last) = n.spine.last() else {
        return match &n.head {
            // A concrete local's identity is its **level**; the arms want the
            // index the syntax domain would have shown, and `var_type` reads
            // Γ by the same index.
            Head::Var(lvl) => TmView::Var(LocalVar(glen(env) - 1 - lvl)),
            // A variable of the abstract prefix: past the concrete entries,
            // so `var_type` misses — which is what the syntax domain does
            // with the same variable.
            Head::BaseVar(d) => TmView::Var(LocalVar(glen(env) + d)),
            Head::Global { var, subst } => TmView::GlobalTm { var: *var, subst },
            _ => TmView::Opaque,
        };
    };
    let head = TmC::value(env, spine_head(n));
    match last {
        Elim::App { dom_level, cod_level, dom, cod, arg } => TmView::App {
            dom_level,
            cod_level,
            dom: TyC::here(env, *dom),
            cod: TyC::under(env, *cod, 1),
            fun: head,
            arg: TmC::here(env, *arg),
        },
        Elim::UApp { levels } => TmView::UApp { levels, fun: head },
        Elim::CtxApp { ctx } => TmView::CtxApp { ctx, fun: head },
        Elim::TyApp { arg } => TmView::TyApp { arg, fun: head },
        Elim::Fst { fst_level, snd_level, fst_ty, snd_ty } => TmView::Fst {
            fst_level,
            snd_level,
            fst_ty: TyC::here(env, *fst_ty),
            snd_ty: TyC::under(env, *snd_ty, 1),
            pair: head,
        },
        Elim::Snd { fst_level, snd_level, fst_ty, snd_ty } => TmView::Snd {
            fst_level,
            snd_level,
            fst_ty: TyC::here(env, *fst_ty),
            snd_ty: TyC::under(env, *snd_ty, 1),
            pair: head,
        },
        Elim::ElimNat { level, motive, base, step } => TmView::ElimNat {
            level,
            motive: TyC::under(env, *motive, 1),
            base: TmC::here(env, *base),
            // The step is scoped in `(Γ, x, y)`, as in reduce.rs.
            step: TmC::under(env, *step, 2),
            scrut: head,
        },
        Elim::ElimEmpty { level, scrut_level, motive } => TmView::ElimEmpty {
            level,
            scrut_level,
            motive: TyC::under(env, *motive, 1),
            scrut: head,
        },
        Elim::ElimSEmpty { level, scrut_level, motive } => TmView::ElimSEmpty {
            level,
            scrut_level,
            motive: TyC::under(env, *motive, 1),
            scrut: head,
        },
        Elim::ElimSquash { src_level, dst_level, src_ty, motive, .. } => {
            TmView::ElimSquash {
                src_level,
                dst_level,
                src_ty: TyC::here(env, *src_ty),
                motive: TyC::under(env, *motive, 1),
                scrut: head,
            }
        }
        Elim::Case {
            lhs_level,
            rhs_level,
            motive_level,
            lhs,
            rhs,
            motive,
            case_l,
            case_r,
        } => TmView::Case {
            lhs_level,
            rhs_level,
            motive_level,
            lhs: TyC::here(env, *lhs),
            rhs: TyC::here(env, *rhs),
            motive: TyC::under(env, *motive, 1),
            case_l: TmC::under(env, *case_l, 1),
            case_r: TmC::under(env, *case_r, 1),
            scrut: head,
        },
        Elim::ElimW {
            shape_level,
            pos_level,
            motive_level,
            shape,
            pos,
            motive,
            step,
            ..
        } => TmView::ElimW {
            shape_level,
            pos_level,
            motive_level,
            shape: TyC::here(env, *shape),
            pos: TyC::under(env, *pos, 1),
            motive: TyC::under(env, *motive, 1),
            // `(Γ, a, f, ih)`.
            step: TmC::under(env, *step, 3),
            scrut: head,
        },
        Elim::ElimWf { level, motive_level, shape, arity, motive, step, .. } => {
            TmView::ElimWf {
                level,
                motive_level,
                shape: TyC::here(env, *shape),
                arity: TmC::under(env, *arity, 1),
                motive: TyC::under(env, *motive, 1),
                // `(Γ, a, cs, ih)`.
                step: TmC::under(env, *step, 3),
                scrut: head,
            }
        }
        Elim::J { ty_level, motive_level, ty, lhs, motive, case, rhs } => TmView::J {
            ty_level,
            motive_level,
            ty: TyC::here(env, *ty),
            lhs: TmC::here(env, *lhs),
            // `(Γ, y, p)`.
            motive: TyC::under(env, *motive, 2),
            case: TmC::here(env, *case),
            rhs: TmC::here(env, *rhs),
            proof: head,
        },
        Elim::Transp { ty_level, motive_level, ty, motive, lhs, rhs, tm } => {
            TmView::Transp {
                ty_level,
                motive_level,
                ty: TyC::here(env, *ty),
                motive: TyC::under(env, *motive, 1),
                lhs: TmC::here(env, *lhs),
                rhs: TmC::here(env, *rhs),
                tm: TmC::here(env, *tm),
            }
        }
        Elim::LetBoxTy { motive_level, code_level, ctx, motive, body } => {
            TmView::LetBoxTy {
                motive_level,
                code_level,
                ctx,
                motive: TyC::under(env, *motive, 1),
                // The body binds a *global*, not a local: no pending local
                // binder, and `under_tele_tm` is what moves it.
                body: TmC::here(env, *body),
                scrut: head,
            }
        }
        Elim::LetBoxTm { motive_level, code_level, ctx, ty, motive, body } => {
            TmView::LetBoxTm {
                motive_level,
                code_level,
                ctx,
                ty,
                motive: TyC::under(env, *motive, 1),
                body: TmC::here(env, *body),
                scrut: head,
            }
        }
        Elim::ElimCodeTy {
            ty_motive_level,
            tm_motive_level,
            motives,
            branches,
            code_level,
            ctx,
            env: renv,
        } => TmView::ElimCodeTy {
            ty_motive_level,
            tm_motive_level,
            motives: Rc::clone(motives),
            branches: Rc::clone(branches),
            code_level,
            ctx,
            scrut: head,
            rec: RecEnv(*renv),
        },
        Elim::ElimCodeTm {
            ty_motive_level,
            tm_motive_level,
            motives,
            branches,
            code_level,
            ctx,
            ty,
            env: renv,
        } => TmView::ElimCodeTm {
            ty_motive_level,
            tm_motive_level,
            motives: Rc::clone(motives),
            branches: Rc::clone(branches),
            code_level,
            ctx,
            ty,
            scrut: head,
            rec: RecEnv(*renv),
        },
    }
}
