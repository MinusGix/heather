//! Weakening a **value** in the two outer namespaces (L and Ψ).
//!
//! Locals go through the environment, so pushing a local binder costs a value
//! nothing (`docs/nbe-conversion-design.md` §3.2: variables are levels).
//! Universe variables and globals are different: they stay *syntax* (§3.1),
//! de Bruijn-indexed from the inner end, so extending L or Ψ renumbers every
//! occurrence — including the ones buried in a closure's captured
//! environment, where the design's original "values need the other-namespace
//! maps" is exactly right.
//!
//! Stage 1's log argued the maps away, and for the **evaluator** that argument
//! holds: entering a `ΠΠ`/`(g:Ctx)⇒`/`(U:Typ)⇒` binder *instantiates*, and
//! `inst_univ`/`apply_global` renumber the outer scope back down, so a
//! captured environment is already in the post-instantiation scope.
//! Conversion is where the argument stops: its four layer-m η arms, the three
//! layer-m type congruences, the two `letbox` arms and every recursor branch
//! telescope **weaken** the outer scope and then compare *under* it. There the
//! body syntax is already scoped in the extended context and the captured
//! environment is not, and the two must be brought back together.
//!
//! Everything here is cold — layer-m metaprogram paths only — and eager: it
//! rebuilds the reachable value graph with every level and every piece of
//! carried syntax shifted. Memos are dropped rather than shifted, which is
//! sound (a memo is a cache) and keeps the map total. Shifting by zero is the
//! identity on the *handle*, so the ordinary program path never pays.

use std::sync::Arc as Rc;

use crate::level::Level;
use crate::term::{Branches, LocalCtx, Motives, Term, Type};

use super::{
    BitTy, Elim, Env, Head, TmClo, TyClo, VNeTy, VNeutral, VSubst, VTy, Val, ValueArena,
};

/// How far to weaken: `univs` new universe variables, `globals` new global
/// bindings, both pushed innermost (which is what `Conv::Env<'v>::push_tele`
/// does).
#[derive(Clone, Copy)]
pub struct Outer<'v> {
    pub arena: &'v ValueArena<'v>,
    pub univs: u32,
    pub globals: u32,
}

impl<'v> Outer<'v> {
    pub fn none(arena: &'v ValueArena<'v>) -> Outer<'v> {
        Outer { arena, univs: 0, globals: 0 }
    }

    pub fn is_none(&self) -> bool {
        self.univs == 0 && self.globals == 0
    }
}

fn level<'v>(l: &Level, o: Outer<'v>) -> Level {
    if o.univs == 0 {
        return l.clone();
    }
    l.shift(o.univs, 0)
}

fn ty_syn<'v>(t: &Rc<Type>, o: Outer<'v>) -> Rc<Type> {
    Rc::new(t.shift_univ(o.univs).shift_global(o.globals))
}

fn tm_syn<'v>(t: &Rc<Term>, o: Outer<'v>) -> Rc<Term> {
    Rc::new(t.shift_univ(o.univs).shift_global(o.globals))
}

fn ctx_syn<'v>(c: &LocalCtx, o: Outer<'v>) -> LocalCtx {
    c.shift_univ(o.univs).shift_global(o.globals)
}

/// The recursor tables, shifted by routing them through the syntax map that
/// already knows all 54 fields: `subst.rs`'s `sub_motives`/`sub_branches` are
/// private, and transcribing them here a *seventh* time is exactly the
/// drift hazard `rec.rs` exists to prevent. The wrapper term is discarded.
fn tables<'v>(m: &Rc<Motives>, b: &Rc<Branches>, o: Outer<'v>) -> (Rc<Motives>, Rc<Branches>) {
    let wrapper = Term::ElimCodeTy {
        ty_motive_level: Level::Zero,
        tm_motive_level: Level::Zero,
        motives: Rc::clone(m),
        branches: Rc::clone(b),
        code_level: Level::Zero,
        ctx: LocalCtx::nil(),
        scrut: Rc::new(Term::Zero),
    };
    let shifted = wrapper.shift_univ(o.univs).shift_global(o.globals);
    let Term::ElimCodeTy { motives, branches, .. } = shifted else {
        unreachable!("shifting an elim^Typ yields an elim^Typ")
    };
    (motives, branches)
}

// ---------------------------------------------------------------------------
// The value graph
// ---------------------------------------------------------------------------

pub fn env<'v>(e: &Env<'v>, o: Outer<'v>) -> Env<'v> {
    if o.is_none() {
        return *e;
    }
    let mut out = Env::empty();
    for c in e.to_vec() {
        out = out.push(o.arena, tm_clo(c, o));
    }
    out
}

pub fn tm_clo<'v>(c: &'v TmClo<'v>, o: Outer<'v>) -> &'v TmClo<'v> {
    if o.is_none() {
        return c;
    }
    o.arena.tm(match c {
        TmClo::Syn { env: e, body, .. } => TmClo::syn(env(e, o), tm_syn(body, o)),
        TmClo::Val(v) => TmClo::val(val(v, o)),
        TmClo::Elim { head, elim, .. } => {
            TmClo::elim(tm_clo(head, o), Rc::new(elimination(elim, o)))
        }
    })
}

pub fn ty_clo<'v>(c: &'v TyClo<'v>, o: Outer<'v>) -> &'v TyClo<'v> {
    if o.is_none() {
        return c;
    }
    o.arena.ty(match c {
        TyClo::Syn { env: e, body, .. } => TyClo::new(env(e, o), ty_syn(body, o)),
        TyClo::Val(v) => TyClo::val(vty(v, o)),
        TyClo::Vec { level: l, elem, len, .. } => {
            return o.arena.ty_vec(level(l, o), ty_clo(elem, o), tm_clo(len, o));
        }
        TyClo::El { level: l, tm, .. } => {
            return o.arena.ty_el(level(l, o), tm_clo(tm, o));
        }
    })
}

/// Weaken only the **captured environment**, leaving the body syntax alone:
/// the body of a `ΠΠ`, a `(g:Ctx)⇒`, a `(U:Typ)⇒` or a `letbox` is already
/// written in the extended scope, and only what it closed over is not.
pub fn reenv_ty<'v>(c: &'v TyClo<'v>, o: Outer<'v>) -> &'v TyClo<'v> {
    if o.is_none() {
        return c;
    }
    match c {
        TyClo::Syn { env: e, body, .. } => {
            o.arena.ty(TyClo::new(env(e, o), Rc::clone(body)))
        }
        _ => ty_clo(c, o),
    }
}

pub fn reenv_tm<'v>(c: &'v TmClo<'v>, o: Outer<'v>) -> &'v TmClo<'v> {
    if o.is_none() {
        return c;
    }
    match c {
        TmClo::Syn { env: e, body, .. } => {
            o.arena.tm(TmClo::syn(env(e, o), Rc::clone(body)))
        }
        _ => tm_clo(c, o),
    }
}

fn vsubst<'v>(d: &VSubst<'v>, o: Outer<'v>) -> VSubst<'v> {
    VSubst {
        tail: d.tail,
        terms: d.terms.iter().map(|t| val(t, o)).collect(),
    }
}

fn head<'v>(h: &Head<'v>, o: Outer<'v>) -> Head<'v> {
    match h {
        Head::Var(l) => Head::Var(*l),
        Head::BaseVar(d) => Head::BaseVar(*d),
        Head::Global { var, subst } => Head::Global {
            // A global *variable* is an index into Ψ, so weakening Ψ
            // renumbers it exactly as `shift_global` renumbers the syntax.
            var: crate::term::GlobalVar(var.0 + o.globals),
            subst: vsubst(subst, o),
        },
        Head::BoxedGlobalTy(t) => Head::BoxedGlobalTy(ty_syn(t, o)),
        Head::BoxedGlobalTm(t) => Head::BoxedGlobalTm(tm_syn(t, o)),
        Head::Stuck(v) => Head::Stuck(val(v, o)),
    }
}

fn elimination<'v>(e: &Elim<'v>, o: Outer<'v>) -> Elim<'v> {
    match e {
        Elim::App { dom_level, cod_level, dom, cod, arg } => Elim::App {
            dom_level: level(dom_level, o),
            cod_level: level(cod_level, o),
            dom: ty_clo(dom, o),
            cod: ty_clo(cod, o),
            arg: tm_clo(arg, o),
        },
        Elim::UApp { levels } => Elim::UApp {
            levels: levels.iter().map(|l| level(l, o)).collect(),
        },
        Elim::CtxApp { ctx } => Elim::CtxApp { ctx: ctx_syn(ctx, o) },
        Elim::TyApp { arg } => Elim::TyApp { arg: ty_syn(arg, o) },
        Elim::Fst { fst_level, snd_level, fst_ty, snd_ty } => Elim::Fst {
            fst_level: level(fst_level, o),
            snd_level: level(snd_level, o),
            fst_ty: ty_clo(fst_ty, o),
            snd_ty: ty_clo(snd_ty, o),
        },
        Elim::Snd { fst_level, snd_level, fst_ty, snd_ty } => Elim::Snd {
            fst_level: level(fst_level, o),
            snd_level: level(snd_level, o),
            fst_ty: ty_clo(fst_ty, o),
            snd_ty: ty_clo(snd_ty, o),
        },
        Elim::ElimNat { level: l, motive, base, step } => Elim::ElimNat {
            level: level(l, o),
            motive: ty_clo(motive, o),
            base: tm_clo(base, o),
            step: tm_clo(step, o),
        },
        Elim::ElimEmpty { level: l, scrut_level, motive } => Elim::ElimEmpty {
            level: level(l, o),
            scrut_level: level(scrut_level, o),
            motive: ty_clo(motive, o),
        },
        Elim::ElimSEmpty { level: l, scrut_level, motive } => Elim::ElimSEmpty {
            level: level(l, o),
            scrut_level: level(scrut_level, o),
            motive: ty_clo(motive, o),
        },
        Elim::ElimSquash { src_level, dst_level, src_ty, motive, case } => {
            Elim::ElimSquash {
                src_level: level(src_level, o),
                dst_level: level(dst_level, o),
                src_ty: ty_clo(src_ty, o),
                motive: ty_clo(motive, o),
                case: tm_clo(case, o),
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
        } => Elim::Case {
            lhs_level: level(lhs_level, o),
            rhs_level: level(rhs_level, o),
            motive_level: level(motive_level, o),
            lhs: ty_clo(lhs, o),
            rhs: ty_clo(rhs, o),
            motive: ty_clo(motive, o),
            case_l: tm_clo(case_l, o),
            case_r: tm_clo(case_r, o),
        },
        Elim::ElimW {
            shape_level,
            pos_level,
            motive_level,
            shape,
            pos,
            motive,
            step,
            env: e,
        } => Elim::ElimW {
            shape_level: level(shape_level, o),
            pos_level: level(pos_level, o),
            motive_level: level(motive_level, o),
            shape: ty_clo(shape, o),
            pos: ty_clo(pos, o),
            motive: ty_clo(motive, o),
            step: tm_clo(step, o),
            env: env(e, o),
        },
        Elim::ElimWf { level: l, motive_level, shape, arity, motive, step, env: e } => {
            Elim::ElimWf {
                level: level(l, o),
                motive_level: level(motive_level, o),
                shape: ty_clo(shape, o),
                arity: tm_clo(arity, o),
                motive: ty_clo(motive, o),
                step: tm_clo(step, o),
                env: env(e, o),
            }
        }
        Elim::J { ty_level, motive_level, ty, lhs, motive, case, rhs } => Elim::J {
            ty_level: level(ty_level, o),
            motive_level: level(motive_level, o),
            ty: ty_clo(ty, o),
            lhs: tm_clo(lhs, o),
            motive: ty_clo(motive, o),
            case: tm_clo(case, o),
            rhs: tm_clo(rhs, o),
        },
        Elim::Transp { ty_level, motive_level, ty, motive, lhs, rhs, tm } => Elim::Transp {
            ty_level: level(ty_level, o),
            motive_level: level(motive_level, o),
            ty: ty_clo(ty, o),
            motive: ty_clo(motive, o),
            lhs: tm_clo(lhs, o),
            rhs: tm_clo(rhs, o),
            tm: tm_clo(tm, o),
        },
        Elim::LetBoxTy { motive_level, code_level, ctx, motive, body } => Elim::LetBoxTy {
            motive_level: level(motive_level, o),
            code_level: level(code_level, o),
            ctx: ctx_syn(ctx, o),
            motive: ty_clo(motive, o),
            body: tm_clo(body, o),
        },
        Elim::LetBoxTm { motive_level, code_level, ctx, ty, motive, body } => {
            Elim::LetBoxTm {
                motive_level: level(motive_level, o),
                code_level: level(code_level, o),
                ctx: ctx_syn(ctx, o),
                ty: ty_syn(ty, o),
                motive: ty_clo(motive, o),
                body: tm_clo(body, o),
            }
        }
        Elim::ElimCodeTy {
            ty_motive_level,
            tm_motive_level,
            motives,
            branches,
            code_level,
            ctx,
            env: e,
        } => {
            let (m, b) = tables(motives, branches, o);
            Elim::ElimCodeTy {
                ty_motive_level: level(ty_motive_level, o),
                tm_motive_level: level(tm_motive_level, o),
                motives: m,
                branches: b,
                code_level: level(code_level, o),
                ctx: ctx_syn(ctx, o),
                env: env(e, o),
            }
        }
        Elim::ElimCodeTm {
            ty_motive_level,
            tm_motive_level,
            motives,
            branches,
            code_level,
            ctx,
            ty,
            env: e,
        } => {
            let (m, b) = tables(motives, branches, o);
            Elim::ElimCodeTm {
                ty_motive_level: level(ty_motive_level, o),
                tm_motive_level: level(tm_motive_level, o),
                motives: m,
                branches: b,
                code_level: level(code_level, o),
                ctx: ctx_syn(ctx, o),
                ty: ty_syn(ty, o),
                env: env(e, o),
            }
        }
    }
}

fn neutral<'v>(n: &Rc<VNeutral<'v>>, o: Outer<'v>) -> Rc<VNeutral<'v>> {
    let mut eliminations: Vec<_> = n.spine.iter_rev().collect();
    eliminations.reverse();
    let mut spine = super::ElimSpine::empty();
    for elim in eliminations {
        spine = o.arena.elim(spine, elimination(elim, o));
    }
    Rc::new(VNeutral {
        head: head(&n.head, o),
        spine,
        unfold: n.unfold.as_ref().map(|u| tm_clo(u, o)),
    })
}

fn nety<'v>(n: &VNeTy<'v>, o: Outer<'v>) -> VNeTy<'v> {
    match n {
        VNeTy::Global { var, subst } => VNeTy::Global {
            var: crate::term::GlobalVar(var.0 + o.globals),
            subst: vsubst(subst, o),
        },
        VNeTy::El { level: l, tm } => VNeTy::El { level: level(l, o), tm: val(tm, o) },
    }
}

pub fn vty<'v>(v: &Rc<VTy<'v>>, o: Outer<'v>) -> Rc<VTy<'v>> {
    if o.is_none() {
        return Rc::clone(v);
    }
    Rc::new(match &**v {
        VTy::Nat => VTy::Nat,
        VTy::Ty(l) => VTy::Ty(level(l, o)),
        VTy::Unit { level: l } => VTy::Unit { level: level(l, o) },
        VTy::Empty { level: l } => VTy::Empty { level: level(l, o) },
        VTy::SEmpty { level: l } => VTy::SEmpty { level: level(l, o) },
        VTy::Squash { level: l, ty } => VTy::Squash {
            level: level(l, o),
            ty: ty_clo(ty, o),
        },
        VTy::Pi { dom_level, cod_level, dom, cod } => VTy::Pi {
            dom_level: level(dom_level, o),
            cod_level: level(cod_level, o),
            dom: ty_clo(dom, o),
            cod: ty_clo(cod, o),
        },
        VTy::Sigma { fst_level, snd_level, fst, snd } => VTy::Sigma {
            fst_level: level(fst_level, o),
            snd_level: level(snd_level, o),
            fst: ty_clo(fst, o),
            snd: ty_clo(snd, o),
        },
        VTy::W { shape_level, pos_level, shape, pos } => VTy::W {
            shape_level: level(shape_level, o),
            pos_level: level(pos_level, o),
            shape: ty_clo(shape, o),
            pos: ty_clo(pos, o),
        },
        VTy::Wf { level: l, shape, arity } => VTy::Wf {
            level: level(l, o),
            shape: ty_clo(shape, o),
            arity: tm_clo(arity, o),
        },
        VTy::Sum { lhs_level, rhs_level, lhs, rhs } => VTy::Sum {
            lhs_level: level(lhs_level, o),
            rhs_level: level(rhs_level, o),
            lhs: ty_clo(lhs, o),
            rhs: ty_clo(rhs, o),
        },
        VTy::Id { level: l, ty, lhs, rhs } => VTy::Id {
            level: level(l, o),
            ty: ty_clo(ty, o),
            lhs: tm_clo(lhs, o),
            rhs: tm_clo(rhs, o),
        },
        VTy::SEq { level: l, ty, lhs, rhs } => VTy::SEq {
            level: level(l, o),
            ty: ty_clo(ty, o),
            lhs: tm_clo(lhs, o),
            rhs: tm_clo(rhs, o),
        },
        VTy::Vec { level: l, elem, len } => VTy::Vec {
            level: level(l, o),
            elem: ty_clo(elem, o),
            len: val(len, o),
        },
        VTy::Fin { len } => VTy::Fin { len: val(len, o) },
        VTy::UPi { num_vars, level: l, body } => VTy::UPi {
            num_vars: *num_vars,
            level: level(l, o),
            body: ty_clo(body, o),
        },
        VTy::CtxPi { level: l, body } => {
            VTy::CtxPi { level: level(l, o), body: ty_clo(body, o) }
        }
        VTy::TyPi { ctx, arg_level, body_level, body } => VTy::TyPi {
            ctx: ctx_syn(ctx, o),
            arg_level: level(arg_level, o),
            body_level: level(body_level, o),
            body: ty_clo(body, o),
        },
        VTy::CodeTy { ctx, level: l } => {
            VTy::CodeTy { ctx: ctx_syn(ctx, o), level: level(l, o) }
        }
        VTy::CodeTm { ctx, ty, level: l } => VTy::CodeTm {
            ctx: ctx_syn(ctx, o),
            ty: ty_syn(ty, o),
            level: level(l, o),
        },
        VTy::Neutral(n) => VTy::Neutral(nety(n, o)),
    })
}

pub fn val<'v>(v: &Rc<Val<'v>>, o: Outer<'v>) -> Rc<Val<'v>> {
    if o.is_none() {
        return Rc::clone(v);
    }
    Rc::new(match &**v {
        Val::TmNat => Val::TmNat,
        Val::TmTy(l) => Val::TmTy(level(l, o)),
        Val::TmUnit { level: l } => Val::TmUnit { level: level(l, o) },
        Val::TmEmpty { level: l } => Val::TmEmpty { level: level(l, o) },
        Val::TmSEmpty { level: l } => Val::TmSEmpty { level: level(l, o) },
        Val::TmSquash { level: l, ty } => Val::TmSquash {
            level: level(l, o),
            ty: tm_clo(ty, o),
        },
        Val::TmPi { dom_level, cod_level, dom, cod } => Val::TmPi {
            dom_level: level(dom_level, o),
            cod_level: level(cod_level, o),
            dom: tm_clo(dom, o),
            cod: tm_clo(cod, o),
        },
        Val::TmSigma { fst_level, snd_level, fst, snd } => Val::TmSigma {
            fst_level: level(fst_level, o),
            snd_level: level(snd_level, o),
            fst: tm_clo(fst, o),
            snd: tm_clo(snd, o),
        },
        Val::TmW { shape_level, pos_level, shape, pos } => Val::TmW {
            shape_level: level(shape_level, o),
            pos_level: level(pos_level, o),
            shape: tm_clo(shape, o),
            pos: tm_clo(pos, o),
        },
        Val::TmWf { level: l, shape, arity } => Val::TmWf {
            level: level(l, o),
            shape: tm_clo(shape, o),
            arity: tm_clo(arity, o),
        },
        Val::TmId { level: l, ty, lhs, rhs } => Val::TmId {
            level: level(l, o),
            ty: tm_clo(ty, o),
            lhs: tm_clo(lhs, o),
            rhs: tm_clo(rhs, o),
        },
        Val::TmSEq { level: l, ty, lhs, rhs } => Val::TmSEq {
            level: level(l, o),
            ty: tm_clo(ty, o),
            lhs: tm_clo(lhs, o),
            rhs: tm_clo(rhs, o),
        },
        Val::TmSum { lhs_level, rhs_level, lhs, rhs } => Val::TmSum {
            lhs_level: level(lhs_level, o),
            rhs_level: level(rhs_level, o),
            lhs: tm_clo(lhs, o),
            rhs: tm_clo(rhs, o),
        },
        Val::TmVec { level: l, elem, len } => Val::TmVec {
            level: level(l, o),
            elem: tm_clo(elem, o),
            len: tm_clo(len, o),
        },
        Val::TmFin { len } => Val::TmFin { len: tm_clo(len, o) },
        Val::Zero => Val::Zero,
        Val::Succ(p) => Val::Succ(tm_clo(p, o)),
        Val::NatRun { program, tail } => Val::NatRun {
            program: Rc::clone(program),
            tail: tm_clo(tail, o),
        },
        // The element type's injections are values in the same two outer
        // namespaces, so a shifted run gets a shifted [`BitTy`]; sharing the
        // memoized one would keep the unshifted injections.
        Val::BitRun { level: l, ty, width, bits, tail_len, tail } => Val::BitRun {
            level: level(l, o),
            ty: o.arena.bit_ty(BitTy {
                elem: ty_clo(ty.elem, o),
                zero: tm_clo(ty.zero, o),
                one: tm_clo(ty.one, o),
            }),
            width: *width,
            bits: *bits,
            tail_len: tm_clo(tail_len, o),
            tail: tm_clo(tail, o),
        },
        Val::NatSync { program, tail, elim } => Val::NatSync {
            program: Rc::clone(program),
            tail: tm_clo(tail, o),
            elim: Rc::new(elimination(elim, o)),
        },
        Val::Refl { level: l, ty, tm } => Val::Refl {
            level: level(l, o),
            ty: ty_clo(ty, o),
            tm: tm_clo(tm, o),
        },
        Val::SRefl { level: l, ty, tm } => Val::SRefl {
            level: level(l, o),
            ty: ty_clo(ty, o),
            tm: tm_clo(tm, o),
        },
        Val::Squash { level: l, ty, tm } => Val::Squash {
            level: level(l, o),
            ty: ty_clo(ty, o),
            tm: tm_clo(tm, o),
        },
        Val::Pair { fst_level, snd_level, fst_ty, snd_ty, fst, snd } => Val::Pair {
            fst_level: level(fst_level, o),
            snd_level: level(snd_level, o),
            fst_ty: ty_clo(fst_ty, o),
            snd_ty: ty_clo(snd_ty, o),
            fst: tm_clo(fst, o),
            snd: tm_clo(snd, o),
        },
        Val::Triv { level: l } => Val::Triv { level: level(l, o) },
        Val::Inl { lhs_level, rhs_level, lhs, rhs, val: v } => Val::Inl {
            lhs_level: level(lhs_level, o),
            rhs_level: level(rhs_level, o),
            lhs: ty_clo(lhs, o),
            rhs: ty_clo(rhs, o),
            val: tm_clo(v, o),
        },
        Val::Inr { lhs_level, rhs_level, lhs, rhs, val: v } => Val::Inr {
            lhs_level: level(lhs_level, o),
            rhs_level: level(rhs_level, o),
            lhs: ty_clo(lhs, o),
            rhs: ty_clo(rhs, o),
            val: tm_clo(v, o),
        },
        Val::Sup { shape_level, pos_level, shape_ty, pos_ty, label, children } => Val::Sup {
            shape_level: level(shape_level, o),
            pos_level: level(pos_level, o),
            shape_ty: ty_clo(shape_ty, o),
            pos_ty: ty_clo(pos_ty, o),
            label: tm_clo(label, o),
            children: tm_clo(children, o),
        },
        Val::Supf { level: l, shape, arity, label, children } => Val::Supf {
            level: level(l, o),
            shape: ty_clo(shape, o),
            arity: tm_clo(arity, o),
            label: tm_clo(label, o),
            children: tm_clo(children, o),
        },
        Val::Lam { dom_level, cod_level, dom, body } => Val::Lam {
            dom_level: level(dom_level, o),
            cod_level: level(cod_level, o),
            dom: ty_clo(dom, o),
            body: tm_clo(body, o),
        },
        // The body of a `Λ` is scoped *under* its own binders, so the outer
        // weakening does not reach the innermost `num_vars` levels — the
        // cutoff `shift_univ_above` exists for. The captured environment is
        // outside them and shifts in full.
        Val::ULam { num_vars, level: l, body } => Val::ULam {
            num_vars: *num_vars,
            level: level(l, o),
            body: shift_under(body, o, *num_vars, 0),
        },
        Val::CtxLam { level: l, body } => Val::CtxLam {
            level: level(l, o),
            body: shift_under(body, o, 0, 1),
        },
        Val::TyLam { ctx, arg_level, body_level, body } => Val::TyLam {
            ctx: ctx_syn(ctx, o),
            arg_level: level(arg_level, o),
            body_level: level(body_level, o),
            body: shift_under(body, o, 0, 1),
        },
        Val::BoxTy(t) => Val::BoxTy(ty_syn(t, o)),
        Val::BoxTm(t) => Val::BoxTm(tm_syn(t, o)),
        Val::Neutral(n) => Val::Neutral(neutral(n, o)),
    })
}

/// A term closure whose **syntax** sits under `cu` universe and `cg` global
/// binders of its own while its **environment** does not: the body shifts
/// above the cutoff, the environment shifts in full.
fn shift_under<'v>(c: &'v TmClo<'v>, o: Outer<'v>, cu: u32, cg: u32) -> &'v TmClo<'v> {
    match c {
        TmClo::Syn { env: e, body, .. } => o.arena.tm(TmClo::syn(
            env(e, o),
            Rc::new(
                body.shift_univ_above(o.univs, cu)
                    .shift_global_above(o.globals, cg),
            ),
        )),
        // Not a syntactic closure: nothing is under the binder, so the
        // ordinary map applies.
        _ => tm_clo(c, o),
    }
}
