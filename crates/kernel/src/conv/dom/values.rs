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

/// The value domain: `Conv<Values>` is the kernel's conversion checker.
pub(crate) struct Values;

// ---------------------------------------------------------------------------
// Carriers
// ---------------------------------------------------------------------------

/// A type sub-structure: a closure plus the two scope lengths of the module
/// docs.
#[derive(Clone)]
pub(crate) struct TyC {
    clo: Rc<TyClo>,
    home: u32,
    sat: u32,
}

/// [`TyC`] for terms.
#[derive(Clone)]
pub(crate) struct TmC {
    clo: Rc<TmClo>,
    home: u32,
    sat: u32,
}

/// The scope a code recursor's Γ-scoped raw syntax is read in: the
/// environment the elimination stored when it was built.
#[derive(Clone)]
pub(crate) struct RecEnv(value::Env);

fn glen(env: &Env) -> u32 {
    env.gamma.entries.len() as u32
}

/// The neutral variable a binder pushed at Γ-length `level` is bound to.
fn fresh(level: u32) -> Rc<TmClo> {
    Rc::new(TmClo::val(Rc::new(Val::var(level))))
}

/// The same variable, taken from the environment that already holds it
/// rather than allocated again — `open_*` asks for it once per binder
/// descent, which is conversion's hottest path.
fn var_at(env: &Env, level: u32) -> Rc<TmClo> {
    let n = env.gamma.entries.len() as u32;
    match n.checked_sub(1 + level).map(|i| env.rho.lookup(i)) {
        Some(value::Lookup::Bound(c)) => c,
        _ => fresh(level),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn type_identity_fast_path_is_scope_sensitive() {
        let body = Type::El {
            level: Level::Zero,
            tm: Rc::new(Term::Var(LocalVar(0))),
        };
        let clo = Rc::new(TyClo::new(value::Env::empty(), Rc::new(body)));
        let a = TyC { clo: Rc::clone(&clo), home: 2, sat: 3 };
        let same = TyC { clo: Rc::clone(&clo), home: 2, sat: 3 };
        let other_home = TyC { clo: Rc::clone(&clo), home: 1, sat: 3 };
        let other_sat = TyC { clo, home: 2, sat: 4 };

        assert!(Values::ty_eq_fast(&a, &same));
        assert!(!Values::ty_eq_fast(&a, &other_home));
        assert!(!Values::ty_eq_fast(&a, &other_sat));
    }
}

impl TyC {
    /// A sub-structure that is a type **here**, in `env`.
    fn here(env: &Env, clo: Rc<TyClo>) -> TyC {
        let n = glen(env);
        TyC { clo, home: n, sat: n }
    }

    /// A sub-structure under `k` of the carrier's own pending binders.
    fn under(env: &Env, clo: Rc<TyClo>, k: u32) -> TyC {
        let n = glen(env);
        TyC { clo, home: n, sat: n + k }
    }

    fn value(env: &Env, v: Rc<VTy>) -> TyC {
        TyC::here(env, Rc::new(TyClo::val(v)))
    }
}

impl TmC {
    fn here(env: &Env, clo: Rc<TmClo>) -> TmC {
        let n = glen(env);
        TmC { clo, home: n, sat: n }
    }

    fn under(env: &Env, clo: Rc<TmClo>, k: u32) -> TmC {
        let n = glen(env);
        TmC { clo, home: n, sat: n + k }
    }

    fn value(env: &Env, v: Rc<Val>) -> TmC {
        TmC::here(env, Rc::new(TmClo::val(v)))
    }
}

/// Apply a type closure to arguments, **without forcing**: a syntactic
/// closure extends its environment, anything else has no pending binders and
/// ignores them.
fn apply_ty_clo(c: &Rc<TyClo>, args: &[Rc<TmClo>]) -> Rc<TyClo> {
    if args.is_empty() {
        return Rc::clone(c);
    }
    match &**c {
        TyClo::Syn { env, body, .. } => Rc::new(TyClo::new(env.extend(args), Rc::clone(body))),
        _ => Rc::clone(c),
    }
}

fn apply_tm_clo(c: &Rc<TmClo>, args: &[Rc<TmClo>]) -> Rc<TmClo> {
    if args.is_empty() {
        return Rc::clone(c);
    }
    match &**c {
        TmClo::Syn { env, body, .. } => Rc::new(TmClo::syn(env.extend(args), Rc::clone(body))),
        _ => Rc::clone(c),
    }
}

/// Make a closure consume — and ignore — `by` more binders, innermost. This
/// is what `shift_local` means on the syntax side, and the reason it is a
/// shift *there* and a nothing *here* is that the body's own free indices
/// have to step over the new cells.
fn weaken_ty_clo(c: &Rc<TyClo>, by: u32) -> Rc<TyClo> {
    if by == 0 {
        return Rc::clone(c);
    }
    match &**c {
        TyClo::Syn { env, body, .. } => {
            Rc::new(TyClo::new(env.clone(), Rc::new(body.shift_local(by))))
        }
        _ => Rc::clone(c),
    }
}

fn weaken_tm_clo(c: &Rc<TmClo>, by: u32) -> Rc<TmClo> {
    if by == 0 {
        return Rc::clone(c);
    }
    match &**c {
        TmClo::Syn { env, body, .. } => {
            Rc::new(TmClo::syn(env.clone(), Rc::new(body.shift_local(by))))
        }
        _ => Rc::clone(c),
    }
}

/// Read a carrier in `env` with `pending` of its binders left for the caller:
/// supply the fresh neutrals of every binder between the carrier's home and
/// that point, weakening first if the carrier is older than the scope.
///
/// This is the one place the two numbers are spent, and it is total by
/// construction: `k` args are supplied for levels `home .. home + k`, which
/// are exactly the levels [`Env::push_entry`] assigned.
fn open_ty(env: &Env, c: &TyC, pending: u32) -> Rc<TyClo> {
    let want = glen(env) + pending;
    let mut clo = Rc::clone(&c.clo);
    let mut sat = c.sat;
    if sat < want {
        clo = weaken_ty_clo(&clo, want - sat);
        sat = want;
    }
    let stop = sat.saturating_sub(pending).min(glen(env));
    if stop > c.home {
        let args: Vec<Rc<TmClo>> = (c.home..stop).map(|l| var_at(env, l)).collect();
        clo = apply_ty_clo(&clo, &args);
    }
    clo
}

fn open_tm(env: &Env, c: &TmC, pending: u32) -> Rc<TmClo> {
    let want = glen(env) + pending;
    let mut clo = Rc::clone(&c.clo);
    let mut sat = c.sat;
    if sat < want {
        clo = weaken_tm_clo(&clo, want - sat);
        sat = want;
    }
    let stop = sat.saturating_sub(pending).min(glen(env));
    if stop > c.home {
        let args: Vec<Rc<TmClo>> = (c.home..stop).map(|l| var_at(env, l)).collect();
        clo = apply_tm_clo(&clo, &args);
    }
    clo
}

/// Run the machine on the checker's own budget. Fuel is a single shared
/// account (design §6): the evaluator spends from it and hands back what is
/// left, so a reduction step and a comparison node cost the same one unit
/// they cost today.
fn run<T>(
    cv: &mut Conv<Values>,
    env: &Env,
    f: impl FnOnce(&mut Eval<'_>) -> Result<T, crate::reduce::OutOfFuel>,
) -> R<T> {
    let defs = cv.defs(env);
    let mut ev = Eval::new(cv.fuel, defs, env.gamma.base);
    let out = f(&mut ev);
    cv.fuel = ev.fuel();
    out.map_err(|_| crate::conv::ConvError::OutOfFuel)
}

/// The definition at the head of a δ-stuck spine: at values it is one read,
/// because a glued neutral *is* the answer the syntactic `delta_head` walks a
/// spine to find (design §5).
fn glued(v: &Rc<Val>) -> Option<GlobalVar> {
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
fn spine_head(n: &Rc<VNeutral>) -> Rc<Val> {
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
    let unfold = match n.unfold.as_ref().map(|u| &**u) {
        Some(TmClo::Elim { head, .. }) => Some(Rc::clone(head)),
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
    /// syntax (`Env::vtys` carries the domain object), only the length and
    /// the base.
    static FILLER: Rc<Type> = Rc::new(Type::Nat);
    static NAT_V: Rc<VTy> = Rc::new(VTy::Nat);
    static ZERO_V: Rc<Val> = Rc::new(Val::Zero);
}

// ---------------------------------------------------------------------------
// The instantiation
// ---------------------------------------------------------------------------

impl Dom for Values {
    type Ty = Rc<VTy>;
    type Tm = Rc<Val>;
    type TyC = TyC;
    type TmC = TmC;
    type Subst = VSubst;
    type RecCtx = RecEnv;

    // -- reduction ----------------------------------------------------------

    fn whnf_ty(cv: &mut Conv<Self>, env: &Env, t: &TyC) -> R<Rc<VTy>> {
        let c = open_ty(env, t, 0);
        run(cv, env, |ev| {
            let v = ev.force_ty(&c)?;
            ev.delta_whnf_ty(v)
        })
    }

    fn whnf_ty_root(cv: &mut Conv<Self>, env: &Env, t: &Type) -> R<Rc<VTy>> {
        run(cv, env, |ev| ev.eval_ty(t, &env.rho))
    }

    fn whnf_tm_root(cv: &mut Conv<Self>, env: &Env, t: &Term) -> R<Rc<Val>> {
        run(cv, env, |ev| ev.eval_tm_ref(t, &env.rho))
    }

    fn whnf_tm(cv: &mut Conv<Self>, env: &Env, t: &TmC) -> R<Rc<Val>> {
        let c = open_tm(env, t, 0);
        run(cv, env, |ev| {
            let v = ev.force(&c)?;
            ev.delta_whnf(v)
        })
    }

    /// Forcing *is* the δ-opaque reduction: a definition becomes a glued
    /// neutral and its unfolding is a thunk nobody has pulled.
    fn whnf_ty_opaque(cv: &mut Conv<Self>, env: &Env, t: &TyC) -> R<Rc<VTy>> {
        let c = open_ty(env, t, 0);
        run(cv, env, |ev| ev.force_ty(&c))
    }

    fn whnf_tm_opaque(cv: &mut Conv<Self>, env: &Env, t: &TmC) -> R<Rc<Val>> {
        let c = open_tm(env, t, 0);
        run(cv, env, |ev| ev.force(&c))
    }

    fn delta_ty(cv: &mut Conv<Self>, env: &Env, w: &Rc<VTy>) -> R<Rc<VTy>> {
        let w = Rc::clone(w);
        run(cv, env, |ev| ev.delta_whnf_ty(w))
    }

    fn delta_tm(cv: &mut Conv<Self>, env: &Env, w: &Rc<Val>) -> R<Rc<Val>> {
        let w = Rc::clone(w);
        run(cv, env, |ev| ev.delta_whnf(w))
    }

    fn delta_head(_cv: &Conv<Self>, _env: &Env, w: &Rc<Val>) -> Option<GlobalVar> {
        glued(w)
    }

    fn delta_head_ty(_cv: &Conv<Self>, _env: &Env, w: &Rc<VTy>) -> Option<GlobalVar> {
        match &**w {
            VTy::Neutral(VNeTy::El { tm, .. }) => glued(tm),
            VTy::Vec { len, .. } | VTy::Fin { len } => glued(len),
            _ => None,
        }
    }

    /// The outermost elimination of the spine — a value's head is its *last*
    /// pushed elimination, where the syntax's is its outermost node.
    fn is_transp(w: &Rc<Val>) -> bool {
        matches!(&**w, Val::Neutral(n) if matches!(n.spine.last(), Some(Elim::Transp { .. })))
    }

    // -- views --------------------------------------------------------------

    fn view_ty<'a>(_cv: &mut Conv<Self>, env: &Env, w: &'a Rc<VTy>) -> TyView<'a, Self> {
        match &**w {
            VTy::Nat => TyView::Nat,
            VTy::Ty(l) => TyView::Ty(l),
            VTy::Unit { level } => TyView::Unit { level },
            VTy::Empty { level } => TyView::Empty { level },
            VTy::SEmpty { level } => TyView::SEmpty { level },
            VTy::Pi { dom_level, cod_level, dom, cod } => TyView::Pi {
                dom_level,
                cod_level,
                dom: TyC::here(env, Rc::clone(dom)),
                cod: TyC::under(env, Rc::clone(cod), 1),
            },
            VTy::Sigma { fst_level, snd_level, fst, snd } => TyView::Sigma {
                fst_level,
                snd_level,
                fst: TyC::here(env, Rc::clone(fst)),
                snd: TyC::under(env, Rc::clone(snd), 1),
            },
            VTy::W { shape_level, pos_level, shape, pos } => TyView::W {
                shape_level,
                pos_level,
                shape: TyC::here(env, Rc::clone(shape)),
                pos: TyC::under(env, Rc::clone(pos), 1),
            },
            VTy::Wf { level, shape, arity } => TyView::Wf {
                level,
                shape: TyC::here(env, Rc::clone(shape)),
                arity: TmC::under(env, Rc::clone(arity), 1),
            },
            VTy::Sum { lhs_level, rhs_level, lhs, rhs } => TyView::Sum {
                lhs_level,
                rhs_level,
                lhs: TyC::here(env, Rc::clone(lhs)),
                rhs: TyC::here(env, Rc::clone(rhs)),
            },
            VTy::Id { level, ty, lhs, rhs } => TyView::Id {
                level,
                ty: TyC::here(env, Rc::clone(ty)),
                lhs: TmC::here(env, Rc::clone(lhs)),
                rhs: TmC::here(env, Rc::clone(rhs)),
            },
            VTy::SEq { level, ty, lhs, rhs } => TyView::SEq {
                level,
                ty: TyC::here(env, Rc::clone(ty)),
                lhs: TmC::here(env, Rc::clone(lhs)),
                rhs: TmC::here(env, Rc::clone(rhs)),
            },
            VTy::Vec { level, elem, len } => TyView::Vec {
                level,
                elem: TyC::here(env, Rc::clone(elem)),
                len: TmC::value(env, Rc::clone(len)),
            },
            VTy::Fin { len } => TyView::Fin { len: TmC::value(env, Rc::clone(len)) },
            VTy::UPi { num_vars, level, body } => TyView::UPi {
                num_vars: *num_vars,
                level,
                body: TyC::here(env, Rc::clone(body)),
            },
            VTy::CtxPi { level, body } => {
                TyView::CtxPi { level, body: TyC::here(env, Rc::clone(body)) }
            }
            VTy::TyPi { ctx, arg_level, body_level, body } => TyView::TyPi {
                ctx,
                arg_level,
                body_level,
                body: TyC::here(env, Rc::clone(body)),
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

    fn view_tm<'a>(_cv: &mut Conv<Self>, env: &Env, w: &'a Rc<Val>) -> TmView<'a, Self> {
        match &**w {
            Val::TmNat => TmView::TmNat,
            Val::TmTy(l) => TmView::TmTy(l),
            Val::TmUnit { level } => TmView::TmUnit { level },
            Val::TmEmpty { level } => TmView::TmEmpty { level },
            Val::TmSEmpty { level } => TmView::TmSEmpty { level },
            Val::TmPi { dom_level, cod_level, dom, cod } => TmView::TmPi {
                dom_level,
                cod_level,
                dom: TmC::here(env, Rc::clone(dom)),
                cod: TmC::under(env, Rc::clone(cod), 1),
            },
            Val::TmSigma { fst_level, snd_level, fst, snd } => TmView::TmSigma {
                fst_level,
                snd_level,
                fst: TmC::here(env, Rc::clone(fst)),
                snd: TmC::under(env, Rc::clone(snd), 1),
            },
            Val::TmW { shape_level, pos_level, shape, pos } => TmView::TmW {
                shape_level,
                pos_level,
                shape: TmC::here(env, Rc::clone(shape)),
                pos: TmC::under(env, Rc::clone(pos), 1),
            },
            Val::TmWf { level, shape, arity } => TmView::TmWf {
                level,
                shape: TmC::here(env, Rc::clone(shape)),
                arity: TmC::under(env, Rc::clone(arity), 1),
            },
            Val::TmId { level, ty, lhs, rhs } => TmView::TmId {
                level,
                ty: TmC::here(env, Rc::clone(ty)),
                lhs: TmC::here(env, Rc::clone(lhs)),
                rhs: TmC::here(env, Rc::clone(rhs)),
            },
            Val::TmSEq { level, ty, lhs, rhs } => TmView::TmSEq {
                level,
                ty: TmC::here(env, Rc::clone(ty)),
                lhs: TmC::here(env, Rc::clone(lhs)),
                rhs: TmC::here(env, Rc::clone(rhs)),
            },
            Val::TmSum { lhs_level, rhs_level, lhs, rhs } => TmView::TmSum {
                lhs_level,
                rhs_level,
                lhs: TmC::here(env, Rc::clone(lhs)),
                rhs: TmC::here(env, Rc::clone(rhs)),
            },
            Val::TmVec { level, elem, len } => TmView::TmVec {
                level,
                elem: TmC::here(env, Rc::clone(elem)),
                len: TmC::here(env, Rc::clone(len)),
            },
            Val::TmFin { len } => TmView::TmFin { len: TmC::here(env, Rc::clone(len)) },

            Val::Zero => TmView::Zero,
            Val::Succ(t) => TmView::Succ(TmC::here(env, Rc::clone(t))),
            Val::Refl { tm, .. } => TmView::Refl { tm: TmC::here(env, Rc::clone(tm)) },
            Val::Inl { val, .. } => TmView::Inl { val: TmC::here(env, Rc::clone(val)) },
            Val::Inr { val, .. } => TmView::Inr { val: TmC::here(env, Rc::clone(val)) },
            Val::Sup { label, children, .. } => TmView::Sup {
                label: TmC::here(env, Rc::clone(label)),
                children: TmC::here(env, Rc::clone(children)),
            },
            Val::Supf { label, children, .. } => TmView::Supf {
                label: TmC::here(env, Rc::clone(label)),
                children: TmC::here(env, Rc::clone(children)),
            },
            Val::BoxTy(t) => TmView::BoxTy(t),
            Val::BoxTm(t) => TmView::BoxTm(t),

            Val::Lam { .. }
            | Val::ULam { .. }
            | Val::CtxLam { .. }
            | Val::TyLam { .. }
            | Val::Pair { .. }
            | Val::Triv { .. }
            | Val::SRefl { .. } => TmView::Opaque,

            Val::Neutral(n) => view_neutral(env, n),
        }
    }

    fn head_tm(cv: &mut Conv<Self>, env: &Env, t: &TmC) -> R<Rc<Val>> {
        let c = open_tm(env, t, 0);
        run(cv, env, |ev| ev.force(&c))
    }

    fn as_child_ty(_cv: &mut Conv<Self>, env: &Env, w: &Rc<VTy>) -> R<TyC> {
        Ok(TyC::value(env, Rc::clone(w)))
    }

    // -- scope --------------------------------------------------------------

    fn push_entry(env: &Env, ty: &TyC, level: &Level) -> Env {
        let vty = open_ty(env, ty, 0);
        env.push_entry(FILLER.with(Rc::clone), vty, level.clone())
    }

    fn push_spec(env: &Env, tele: &rec::Tele) -> Env {
        let mut e = env.push_tele(tele.univs, tele.globals.clone());
        for (ty, level) in &tele.locals {
            let vty = Rc::new(TyClo::new(e.rho.clone(), Rc::clone(ty)));
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
    fn var_type(_cv: &mut Conv<Self>, env: &Env, x: LocalVar) -> R<(TyC, Level)> {
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
            return Ok((TyC::here(env, Rc::clone(clo)), level.clone()));
        }
        let Some(e) = env.gamma.entries.nth_inner(x.0) else {
            return Err(NC);
        };
        let clo = Rc::new(TyClo::new(value::Env::identity(i), Rc::clone(&e.ty)));
        Ok((TyC::here(env, clo), e.level.clone()))
    }

    fn weaken_ty(t: &TyC, by: u32) -> TyC {
        TyC {
            clo: weaken_ty_clo(&t.clo, by),
            home: t.home,
            sat: t.sat + by,
        }
    }

    fn weaken_tm(t: &TmC, by: u32) -> TmC {
        TmC {
            clo: weaken_tm_clo(&t.clo, by),
            home: t.home,
            sat: t.sat + by,
        }
    }

    // -- embedding ----------------------------------------------------------

    fn embed_ty(env: &Env, t: Rc<Type>) -> TyC {
        TyC::here(env, Rc::new(TyClo::new(env.rho.clone(), t)))
    }

    /// Raw syntax scoped in Γ-plus-telescope, read in the recursor's own
    /// environment: the stored environment is carried across the telescope
    /// [`Dom::push_spec`] just pushed — weakened in the outer namespaces,
    /// extended by the telescope's local binders.
    fn embed_ty_at(rec: &RecEnv, env: &Env, t: Rc<Type>) -> TyC {
        TyC::here(env, Rc::new(TyClo::new(rec_env(rec, env), t)))
    }

    fn embed_tm_at(rec: &RecEnv, env: &Env, t: Rc<Term>) -> TmC {
        TmC::here(env, Rc::new(TmClo::syn(rec_env(rec, env), t)))
    }

    // -- instantiation ------------------------------------------------------

    /// Closure application, which is why this could not stay at the call
    /// sites: the identity substitution the syntax domain builds is exactly
    /// the environment the closure already has.
    fn inst_ty(
        _cv: &mut Conv<Self>,
        home: &Env,
        cur: &Env,
        m: &TyC,
        args: &[TmC],
    ) -> R<TyC> {
        let k = args.len() as u32;
        let clo = open_ty(home, m, k);
        let vals: Vec<Rc<TmClo>> = args.iter().map(|a| open_tm(cur, a, 0)).collect();
        Ok(TyC::here(cur, apply_ty_clo(&clo, &vals)))
    }

    fn inst_tm(
        _cv: &mut Conv<Self>,
        home: &Env,
        cur: &Env,
        m: &TmC,
        args: &[TmC],
    ) -> R<TmC> {
        let k = args.len() as u32;
        let clo = open_tm(home, m, k);
        let vals: Vec<Rc<TmClo>> = args.iter().map(|a| open_tm(cur, a, 0)).collect();
        Ok(TmC::here(cur, apply_tm_clo(&clo, &vals)))
    }

    fn shift_global_ty(_cv: &mut Conv<Self>, _env: &Env, t: &TyC, by: u32) -> R<TyC> {
        let o = Outer { univs: 0, globals: by };
        Ok(TyC { clo: value::shift::ty_clo(&t.clo, o), home: t.home, sat: t.sat })
    }

    /// Instantiating a `ΠΠ` binder leaves the captured environment alone:
    /// `inst_univ` renumbers the outer scope back *down*, so the environment
    /// is already in the post-instantiation scope (stage 1's log, note 4).
    fn inst_univ_ty(_cv: &mut Conv<Self>, env: &Env, body: &TyC, phi: &[Level]) -> R<TyC> {
        let Some((benv, bbody)) = body.clo.as_syn() else {
            return Err(NC);
        };
        Ok(TyC::here(
            env,
            Rc::new(TyClo::new(benv.clone(), Rc::new(bbody.inst_univ(phi)))),
        ))
    }

    fn inst_ctx_ty(_cv: &mut Conv<Self>, env: &Env, body: &TyC, ctx: &LocalCtx) -> R<TyC> {
        inst_global_ty(env, body, GlobalSubst::single(GlobalEntry::Ctx(ctx.clone())))
    }

    fn inst_tyarg_ty(_cv: &mut Conv<Self>, env: &Env, body: &TyC, arg: &Rc<Type>) -> R<TyC> {
        inst_global_ty(env, body, GlobalSubst::single(GlobalEntry::Ty(Rc::clone(arg))))
    }

    fn under_tele_ty(_cv: &mut Conv<Self>, _env: &Env, t: &TyC, tu: u32, tg: u32) -> R<TyC> {
        let o = Outer { univs: tu, globals: tg };
        Ok(TyC { clo: value::shift::reenv_ty(&t.clo, o), home: t.home, sat: t.sat })
    }

    fn under_tele_tm(_cv: &mut Conv<Self>, _env: &Env, t: &TmC, tu: u32, tg: u32) -> R<TmC> {
        let o = Outer { univs: tu, globals: tg };
        Ok(TmC { clo: value::shift::reenv_tm(&t.clo, o), home: t.home, sat: t.sat })
    }

    // -- local substitutions ------------------------------------------------

    fn subst_len(d: &VSubst) -> usize {
        d.terms.len()
    }

    fn subst_term(env: &Env, d: &VSubst, k: usize) -> TmC {
        TmC::value(env, Rc::clone(&d.terms[k]))
    }

    /// `VTail`'s coarser test: the source context's length and `·`'s base are
    /// dropped, because an environment machine — having substituted nothing —
    /// never renormalizes them, and both are determined by the scope, which
    /// the two sides of a comparison share (stage 1's log, note 2).
    fn subst_tails_agree(a: &VSubst, b: &VSubst) -> bool {
        a.tail == b.tail
    }

    /// `T[δ|ₖ]` — the target-context entry type read under the first `k`
    /// payloads. Those payloads are already values; past them the lookup
    /// falls through to the abstract prefix either way (`eval.rs`'s note on
    /// `global_tm`).
    fn apply_subst_ty(
        _cv: &mut Conv<Self>,
        env: &Env,
        d: &VSubst,
        k: usize,
        t: &Rc<Type>,
    ) -> R<TyC> {
        let mut e = value::Env::empty();
        for v in &d.terms[..k] {
            e = e.push(Rc::new(TmClo::val(Rc::clone(v))));
        }
        Ok(TyC::here(env, Rc::new(TyClo::new(e, Rc::clone(t)))))
    }

    // -- synthesized types --------------------------------------------------

    fn nat() -> TyC {
        TyC { clo: Rc::new(TyClo::val(NAT_V.with(Rc::clone))), home: 0, sat: 0 }
    }

    fn univ(env: &Env, level: &Level) -> TyC {
        TyC::value(env, Rc::new(VTy::Ty(level.clone())))
    }

    fn empty(env: &Env, level: &Level) -> TyC {
        TyC::value(env, Rc::new(VTy::Empty { level: level.clone() }))
    }

    fn sempty(env: &Env, level: &Level) -> TyC {
        TyC::value(env, Rc::new(VTy::SEmpty { level: level.clone() }))
    }

    fn code_ty(env: &Env, ctx: &LocalCtx, level: &Level) -> TyC {
        TyC::value(
            env,
            Rc::new(VTy::CodeTy { ctx: ctx.clone(), level: level.clone() }),
        )
    }

    fn code_tm(env: &Env, ctx: &LocalCtx, ty: &Rc<Type>, level: &Level) -> TyC {
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
    fn el(_cv: &mut Conv<Self>, env: &Env, level: &Level, tm: &TmC) -> R<TyC> {
        let c = open_tm(env, tm, 0);
        Ok(TyC::here(env, Rc::new(TyClo::el(level.clone(), c))))
    }

    fn pi(
        _cv: &mut Conv<Self>,
        env: &Env,
        dom_level: &Level,
        cod_level: &Level,
        dom: &TyC,
        cod: &TyC,
    ) -> R<TyC> {
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
        _cv: &mut Conv<Self>,
        env: &Env,
        lhs_level: &Level,
        rhs_level: &Level,
        lhs: &TyC,
        rhs: &TyC,
    ) -> R<TyC> {
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
        _cv: &mut Conv<Self>,
        env: &Env,
        shape_level: &Level,
        pos_level: &Level,
        shape: &TyC,
        pos: &TyC,
    ) -> R<TyC> {
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
        _cv: &mut Conv<Self>,
        env: &Env,
        level: &Level,
        shape: &TyC,
        arity: &TmC,
    ) -> R<TyC> {
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
        _cv: &mut Conv<Self>,
        env: &Env,
        level: &Level,
        elem: &TyC,
        len: &TmC,
    ) -> R<TyC> {
        Ok(TyC::here(
            env,
            Rc::new(TyClo::vec(
                level.clone(),
                open_ty(env, elem, 0),
                open_tm(env, len, 0),
            )),
        ))
    }

    fn id(
        _cv: &mut Conv<Self>,
        env: &Env,
        level: &Level,
        ty: &TyC,
        lhs: &TmC,
        rhs: &TmC,
    ) -> R<TyC> {
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

    fn zero() -> TmC {
        TmC { clo: Rc::new(TmClo::val(ZERO_V.with(Rc::clone))), home: 0, sat: 0 }
    }

    fn succ(_cv: &mut Conv<Self>, env: &Env, t: &TmC) -> R<TmC> {
        Ok(TmC::value(
            env,
            Rc::new(Val::Succ(open_tm(env, t, 0))),
        ))
    }

    fn local(env: &Env, x: LocalVar) -> TmC {
        let n = glen(env);
        let v = match n.checked_sub(1 + x.0) {
            Some(level) => Val::var(level),
            None => Val::base_var(x.0 - n),
        };
        TmC::value(env, Rc::new(v))
    }

    fn refl(
        _cv: &mut Conv<Self>,
        env: &Env,
        level: &Level,
        ty: &TyC,
        tm: &TmC,
    ) -> R<TmC> {
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
        _cv: &mut Conv<Self>,
        env: &Env,
        left: bool,
        lhs_level: &Level,
        rhs_level: &Level,
        lhs: &TyC,
        rhs: &TyC,
        val: &TmC,
    ) -> R<TmC> {
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
        cv: &mut Conv<Self>,
        env: &Env,
        w: &TyC,
        _by: u32,
        label: &TmC,
        children: &TmC,
    ) -> R<TmC> {
        let wv = Self::whnf_ty(cv, env, w)?;
        let VTy::W { shape_level, pos_level, shape, pos } = &*wv else {
            return Err(NC);
        };
        Ok(TmC::value(
            env,
            Rc::new(Val::Sup {
                shape_level: shape_level.clone(),
                pos_level: pos_level.clone(),
                shape_ty: Rc::clone(shape),
                pos_ty: Rc::clone(pos),
                label: open_tm(env, label, 0),
                children: open_tm(env, children, 0),
            }),
        ))
    }

    /// Pointer equality only: `false` is always safe, and two sub-structures
    /// that are the same object are definitionally the same type.
    fn ty_eq_fast(a: &TyC, b: &TyC) -> bool {
        a.home == b.home && a.sat == b.sat && Rc::ptr_eq(&a.clo, &b.clo)
    }

    /// Pointer equality only: `false` is always safe, and two sub-structures
    /// that are the same object are the commonest case the strip loop meets.
    fn tm_eq_fast(a: &TmC, b: &TmC) -> bool {
        Rc::ptr_eq(&a.clo, &b.clo)
    }

    fn app(
        cv: &mut Conv<Self>,
        env: &Env,
        dom_level: &Level,
        cod_level: &Level,
        dom: &TyC,
        cod: &TyC,
        fun: &TmC,
        arg: &TmC,
    ) -> R<TmC> {
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
        cv: &mut Conv<Self>,
        env: &Env,
        first: bool,
        fst_level: &Level,
        snd_level: &Level,
        fst_ty: &TyC,
        snd_ty: &TyC,
        pair: &TmC,
    ) -> R<TmC> {
        let e = proj_elim(env, first, fst_level, snd_level, fst_ty, snd_ty);
        let p = open_tm(env, pair, 0);
        let v = run(cv, env, |ev| {
            let p = ev.force(&p)?;
            ev.elim(p, e)
        })?;
        Ok(TmC::value(env, v))
    }

    fn box_ty(env: &Env, code: Rc<Type>) -> TmC {
        TmC::value(env, Rc::new(Val::BoxTy(code)))
    }

    fn box_tm(env: &Env, code: Rc<Term>) -> TmC {
        TmC::value(env, Rc::new(Val::BoxTm(code)))
    }

    fn box_ty_payload(cv: &mut Conv<Self>, env: &Env, t: &TmC) -> R<Option<Rc<Type>>> {
        let v = Self::head_tm(cv, env, t)?;
        Ok(match &*v {
            Val::BoxTy(c) => Some(Rc::clone(c)),
            _ => None,
        })
    }

    fn box_tm_payload(cv: &mut Conv<Self>, env: &Env, t: &TmC) -> R<Option<Rc<Term>>> {
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
        cv: &mut Conv<Self>,
        outer: &Env,
        inner: &Env,
        a: &Rc<Val>,
        b: &Rc<Val>,
        dom_level: &Level,
        cod_level: &Level,
        dom: &TyC,
        cod: &TyC,
    ) -> R<(TmC, TmC)> {
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
        cv: &mut Conv<Self>,
        _outer: &Env,
        inner: &Env,
        a: &Rc<Val>,
        b: &Rc<Val>,
        num_vars: u32,
    ) -> R<(TmC, TmC)> {
        let o = Outer { univs: num_vars, globals: 0 };
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
        cv: &mut Conv<Self>,
        _outer: &Env,
        inner: &Env,
        a: &Rc<Val>,
        b: &Rc<Val>,
    ) -> R<(TmC, TmC)> {
        let o = Outer { univs: 0, globals: 1 };
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
        cv: &mut Conv<Self>,
        _outer: &Env,
        inner: &Env,
        a: &Rc<Val>,
        b: &Rc<Val>,
        ctx: &LocalCtx,
    ) -> R<(TmC, TmC)> {
        let o = Outer { univs: 0, globals: 1 };
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
        cv: &mut Conv<Self>,
        env: &Env,
        first: bool,
        a: &Rc<Val>,
        b: &Rc<Val>,
        fst_level: &Level,
        snd_level: &Level,
        fst_ty: &TyC,
        snd_ty: &TyC,
    ) -> R<(TmC, TmC)> {
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
        _cv: &mut Conv<Self>,
        env: &Env,
        level: &Level,
        motive_level: &Level,
        shape: &TyC,
        arity: &TmC,
        motive: &TyC,
    ) -> R<(TyC, TyC, TyC)> {
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
        let e1 = senv.push(fresh(l));
        let e2 = e1.push(fresh(l + 1));
        let e3 = e2.push(fresh(l + 2));
        Ok((
            TyC { clo: Rc::new(TyClo::new(e1, Rc::new(cs))), home: l + 1, sat: l + 1 },
            TyC { clo: Rc::new(TyClo::new(e2, Rc::new(ih))), home: l + 2, sat: l + 2 },
            TyC { clo: Rc::new(TyClo::new(e3, Rc::new(step))), home: l + 3, sat: l + 3 },
        ))
    }

    /// `M_Typ[l/ℓ, Δ/g, t/x_T]`. The universe and global halves are syntactic
    /// (design §3.1); the local half — `M[…]` at the scrutinee under `id_Γ` —
    /// is one environment cell.
    fn inst_ty_motive(
        _cv: &mut Conv<Self>,
        env: &Env,
        rec: &RecEnv,
        motive: &Rc<Type>,
        code_level: &Level,
        ctx: &LocalCtx,
        scrut: &TmC,
    ) -> R<TyC> {
        let body = motive
            .inst_univ(&[code_level.clone()])
            .apply_global(&GlobalSubst::single(GlobalEntry::Ctx(ctx.clone())));
        let e = rec.0.push(open_tm(env, scrut, 0));
        Ok(TyC::here(env, Rc::new(TyClo::new(e, Rc::new(body)))))
    }

    fn inst_tm_motive(
        _cv: &mut Conv<Self>,
        env: &Env,
        rec: &RecEnv,
        motive: &Rc<Type>,
        code_level: &Level,
        ctx: &LocalCtx,
        ty: &Rc<Type>,
        scrut: &TmC,
    ) -> R<TyC> {
        let body = motive.inst_univ(&[code_level.clone()]).apply_global(&GlobalSubst {
            entries: vec![
                GlobalEntry::Ctx(ctx.clone()),
                GlobalEntry::Ty(Rc::clone(ty)),
            ],
        });
        let e = rec.0.push(open_tm(env, scrut, 0));
        Ok(TyC::here(env, Rc::new(TyClo::new(e, Rc::new(body)))))
    }
}

// ---------------------------------------------------------------------------
// Helpers the impl shares
// ---------------------------------------------------------------------------

fn inst_global_ty(env: &Env, body: &TyC, sigma: GlobalSubst) -> R<TyC> {
    let Some((benv, bbody)) = body.clo.as_syn() else {
        return Err(NC);
    };
    Ok(TyC::here(
        env,
        Rc::new(TyClo::new(benv.clone(), Rc::new(bbody.apply_global(&sigma)))),
    ))
}

fn proj_elim(
    env: &Env,
    first: bool,
    fst_level: &Level,
    snd_level: &Level,
    fst_ty: &TyC,
    snd_ty: &TyC,
) -> Elim {
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
fn rec_env(rec: &RecEnv, env: &Env) -> value::Env {
    let (tu, tg, tl) = env.tele;
    let mut e = value::shift::env(&rec.0, Outer { univs: tu, globals: tg });
    let base = glen(env) - tl;
    for i in 0..tl {
        e = e.push(fresh(base + i));
    }
    e
}

/// A neutral's view: its outermost elimination, with the shorter spine as the
/// function or scrutinee. The empty spine is the head itself.
fn view_neutral<'a>(env: &Env, n: &'a Rc<VNeutral>) -> TmView<'a, Values> {
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
            dom: TyC::here(env, Rc::clone(dom)),
            cod: TyC::under(env, Rc::clone(cod), 1),
            fun: head,
            arg: TmC::here(env, Rc::clone(arg)),
        },
        Elim::UApp { levels } => TmView::UApp { levels, fun: head },
        Elim::CtxApp { ctx } => TmView::CtxApp { ctx, fun: head },
        Elim::TyApp { arg } => TmView::TyApp { arg, fun: head },
        Elim::Fst { fst_level, snd_level, fst_ty, snd_ty } => TmView::Fst {
            fst_level,
            snd_level,
            fst_ty: TyC::here(env, Rc::clone(fst_ty)),
            snd_ty: TyC::under(env, Rc::clone(snd_ty), 1),
            pair: head,
        },
        Elim::Snd { fst_level, snd_level, fst_ty, snd_ty } => TmView::Snd {
            fst_level,
            snd_level,
            fst_ty: TyC::here(env, Rc::clone(fst_ty)),
            snd_ty: TyC::under(env, Rc::clone(snd_ty), 1),
            pair: head,
        },
        Elim::ElimNat { level, motive, base, step } => TmView::ElimNat {
            level,
            motive: TyC::under(env, Rc::clone(motive), 1),
            base: TmC::here(env, Rc::clone(base)),
            // The step is scoped in `(Γ, x, y)`, as in reduce.rs.
            step: TmC::under(env, Rc::clone(step), 2),
            scrut: head,
        },
        Elim::ElimEmpty { level, scrut_level, motive } => TmView::ElimEmpty {
            level,
            scrut_level,
            motive: TyC::under(env, Rc::clone(motive), 1),
            scrut: head,
        },
        Elim::ElimSEmpty { level, scrut_level, motive } => TmView::ElimSEmpty {
            level,
            scrut_level,
            motive: TyC::under(env, Rc::clone(motive), 1),
            scrut: head,
        },
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
            lhs: TyC::here(env, Rc::clone(lhs)),
            rhs: TyC::here(env, Rc::clone(rhs)),
            motive: TyC::under(env, Rc::clone(motive), 1),
            case_l: TmC::under(env, Rc::clone(case_l), 1),
            case_r: TmC::under(env, Rc::clone(case_r), 1),
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
            shape: TyC::here(env, Rc::clone(shape)),
            pos: TyC::under(env, Rc::clone(pos), 1),
            motive: TyC::under(env, Rc::clone(motive), 1),
            // `(Γ, a, f, ih)`.
            step: TmC::under(env, Rc::clone(step), 3),
            scrut: head,
        },
        Elim::ElimWf { level, motive_level, shape, arity, motive, step, .. } => {
            TmView::ElimWf {
                level,
                motive_level,
                shape: TyC::here(env, Rc::clone(shape)),
                arity: TmC::under(env, Rc::clone(arity), 1),
                motive: TyC::under(env, Rc::clone(motive), 1),
                // `(Γ, a, cs, ih)`.
                step: TmC::under(env, Rc::clone(step), 3),
                scrut: head,
            }
        }
        Elim::J { ty_level, motive_level, ty, lhs, motive, case, rhs } => TmView::J {
            ty_level,
            motive_level,
            ty: TyC::here(env, Rc::clone(ty)),
            lhs: TmC::here(env, Rc::clone(lhs)),
            // `(Γ, y, p)`.
            motive: TyC::under(env, Rc::clone(motive), 2),
            case: TmC::here(env, Rc::clone(case)),
            rhs: TmC::here(env, Rc::clone(rhs)),
            proof: head,
        },
        Elim::Transp { ty_level, motive_level, ty, motive, lhs, rhs, tm } => {
            TmView::Transp {
                ty_level,
                motive_level,
                ty: TyC::here(env, Rc::clone(ty)),
                motive: TyC::under(env, Rc::clone(motive), 1),
                lhs: TmC::here(env, Rc::clone(lhs)),
                rhs: TmC::here(env, Rc::clone(rhs)),
                tm: TmC::here(env, Rc::clone(tm)),
            }
        }
        Elim::LetBoxTy { motive_level, code_level, ctx, motive, body } => {
            TmView::LetBoxTy {
                motive_level,
                code_level,
                ctx,
                motive: TyC::under(env, Rc::clone(motive), 1),
                // The body binds a *global*, not a local: no pending local
                // binder, and `under_tele_tm` is what moves it.
                body: TmC::here(env, Rc::clone(body)),
                scrut: head,
            }
        }
        Elim::LetBoxTm { motive_level, code_level, ctx, ty, motive, body } => {
            TmView::LetBoxTm {
                motive_level,
                code_level,
                ctx,
                ty,
                motive: TyC::under(env, Rc::clone(motive), 1),
                body: TmC::here(env, Rc::clone(body)),
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
            rec: RecEnv(renv.clone()),
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
            rec: RecEnv(renv.clone()),
        },
    }
}
