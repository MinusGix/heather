//! The code-recursor telescopes of ch. 04 (§More Typing and Equivalence
//! Judgments): the two motive scopes `G_M` and the 37 branch telescopes
//! `G_Typ G_Trm` (13 from ch. 04 plus the Id/Σ/Unit/Empty/Sum/W extension
//! branches of kernel-v1-extensions), each with its expected
//! (motive-instantiated) type.
//!
//! This is the single most error-prone part of the theory, so the tables
//! live here **once** and are consumed by both the convertibility checker
//! ([`crate::conv`], comparing branches pairwise at these types) and the
//! type checker ([`crate::typing`], checking branches against these types).
//! They must also stay in sync with `subst.rs`'s `map_branches` depths and
//! `reduce.rs`'s β-instantiations (checked against docs/delam/04 by review,
//! and exercised end-to-end by the identity-recursor typing test).
//!
//! Scoping convention for a telescope `(ℓ⃗; B⃗; x⃗)`: `univs` universe binders
//! are pushed first, then the global bindings (each scoped over `L, ℓ⃗` and
//! its Ψ-prefix), then the recursive-call local entries (each scoped over
//! the whole telescope plus the previous locals, with the ambient Γ already
//! weakened into the telescope).

use std::rc::Rc;

use crate::layer::Layer;
use crate::level::{Level, UnivVar};
use crate::subst::{GlobalEntry, GlobalSubst};
use crate::term::{
    Branches, CtxBase, CtxEntry, GlobalBinding, GlobalCtx, GlobalVar, LocalCtx, LocalSubst,
    LocalVar, Motives, Term, Type,
};

// ---------------------------------------------------------------------------
// Small constructors
// ---------------------------------------------------------------------------

pub(crate) fn lvar(i: u32) -> Level {
    Level::Var(UnivVar(i))
}

/// The context `g` for the context variable at de Bruijn index `i`.
pub(crate) fn g_ctx(i: u32) -> LocalCtx {
    LocalCtx { base: CtxBase::Var(GlobalVar(i)), entries: vec![] }
}

/// `Δ, x : T @ l`.
pub(crate) fn ext_ctx(base: &LocalCtx, ty: Type, level: Level) -> LocalCtx {
    let mut c = base.clone();
    c.entries.push(CtxEntry { ty: Rc::new(ty), level });
    c
}

/// `U^{id_Δ}` for the global type variable `var` with index context `ctx`.
pub(crate) fn gty(var: u32, ctx: &LocalCtx) -> Type {
    Type::GlobalTy { var: GlobalVar(var), subst: LocalSubst::id(ctx) }
}

/// `u^{id_Δ}` for the global term variable `var` with index context `ctx`.
pub(crate) fn gtm(var: u32, ctx: &LocalCtx) -> Term {
    Term::GlobalTm { var: GlobalVar(var), subst: LocalSubst::id(ctx) }
}

/// Weaken every binding of Ψ by `by` universe variables (all bindings are
/// scoped in the same L).
pub(crate) fn shift_univ_psi(psi: &GlobalCtx, by: u32) -> GlobalCtx {
    if by == 0 {
        return psi.clone();
    }
    GlobalCtx {
        bindings: psi
            .bindings
            .iter()
            .map(|b| match b {
                GlobalBinding::Ctx => GlobalBinding::Ctx,
                GlobalBinding::Ty { ctx, layer, level } => GlobalBinding::Ty {
                    ctx: ctx.shift_univ(by),
                    layer: *layer,
                    level: level.shift(by, 0),
                },
                GlobalBinding::Tm { ctx, layer, ty, level } => GlobalBinding::Tm {
                    ctx: ctx.shift_univ(by),
                    layer: *layer,
                    ty: Rc::new(ty.shift_univ(by)),
                    level: level.shift(by, 0),
                },
            })
            .collect(),
    }
}

// ---------------------------------------------------------------------------
// Motive instantiation (the `M[…/ℓ, …/g, …]` substitutions of ch. 04)
// ---------------------------------------------------------------------------

/// `M_Typ[lp/ℓ, gp/g, xp/x_T]`, viewed under a branch telescope that pushed
/// `tu` universe, `tg` global and `tl` local binders. `M_Typ` is scoped in
/// `(L, ℓ; Ψ, g; Γ, x_T)`; `gamma_tele` is the ambient Γ already weakened
/// into the telescope scope; the payloads are scoped in the telescope.
pub(crate) fn inst_ty_motive(
    m: &Type,
    (tu, tg, tl): (u32, u32, u32),
    lp: Level,
    gp: LocalCtx,
    xp: Term,
    gamma_tele: &LocalCtx,
) -> Type {
    m.shift_univ_above(tu, 1)
        .shift_global_above(tg, 1)
        .inst_univ(&[lp])
        .apply_global(&GlobalSubst::single(GlobalEntry::Ctx(gp)))
        .apply_local(&LocalSubst::id(gamma_tele).shift_local(tl).extended(Rc::new(xp)))
}

/// `M_Trm[lp/ℓ, gp/g, up/U_T, xp/x_t]`, as [`inst_ty_motive`] but for the
/// term motive's telescope `(L, ℓ; Ψ, g, U_T; Γ, x_t)`.
#[allow(clippy::too_many_arguments)]
pub(crate) fn inst_tm_motive(
    m: &Type,
    (tu, tg, tl): (u32, u32, u32),
    lp: Level,
    gp: LocalCtx,
    up: Type,
    xp: Term,
    gamma_tele: &LocalCtx,
) -> Type {
    m.shift_univ_above(tu, 1)
        .shift_global_above(tg, 2)
        .inst_univ(&[lp])
        .apply_global(&GlobalSubst {
            entries: vec![GlobalEntry::Ctx(gp), GlobalEntry::Ty(Rc::new(up))],
        })
        .apply_local(&LocalSubst::id(gamma_tele).shift_local(tl).extended(Rc::new(xp)))
}

// ---------------------------------------------------------------------------
// Telescopes
// ---------------------------------------------------------------------------

/// A branch/motive telescope (see the module docs for scoping).
pub(crate) struct Tele {
    pub univs: u32,
    pub globals: Vec<GlobalBinding>,
    /// Recursive-call entries `(type, level)`, innermost-last.
    pub locals: Vec<(Rc<Type>, Level)>,
}

/// A telescope together with the judgment expected under it: for motives the
/// motive's universe level, for branches the branch's expected type and
/// level.
pub(crate) struct MotiveSpec {
    pub tele: Tele,
    pub level: Level,
}

pub(crate) struct BranchSpec {
    pub tele: Tele,
    pub ty: Rc<Type>,
    pub level: Level,
}

/// The two `G_M` scopes: where `M_Typ` and `M_Trm` live and their levels.
///
/// - `M_Typ`: `Ψ, g; Γ, x_T : □(g ⊢ Ty ℓ) @ 0; L, ℓ ⊢ M_Typ @ l₁`
/// - `M_Trm`: `Ψ, g, U_T : Typ_p(g, ℓ); Γ, x_t : □(g ⊢ U_T^id @ ℓ) @ 0; L, ℓ
///   ⊢ M_Trm @ l₂`
pub(crate) fn motive_specs(l1: &Level, l2: &Level) -> [MotiveSpec; 2] {
    [
        MotiveSpec {
            tele: Tele {
                univs: 1,
                globals: vec![GlobalBinding::Ctx],
                locals: vec![(
                    Rc::new(Type::CodeTy { ctx: g_ctx(0), level: lvar(0) }),
                    Level::Zero,
                )],
            },
            level: l1.shift(1, 0),
        },
        MotiveSpec {
            tele: Tele {
                univs: 1,
                globals: vec![
                    GlobalBinding::Ctx,
                    GlobalBinding::Ty { ctx: g_ctx(0), layer: Layer::Prog, level: lvar(0) },
                ],
                locals: vec![(
                    Rc::new(Type::CodeTm {
                        ctx: g_ctx(1),
                        ty: Rc::new(gty(0, &g_ctx(1))),
                        level: lvar(0),
                    }),
                    Level::Zero,
                )],
            },
            level: l2.shift(1, 0),
        },
    ]
}

/// The two motives, in [`motive_specs`] order.
pub(crate) fn motive_types(m: &Motives) -> [&Rc<Type>; 2] {
    [&m.ty_motive, &m.tm_motive]
}

/// The 37 branches, in [`branch_specs`] order (= `Branches` field order).
pub(crate) fn branch_terms(b: &Branches) -> [&Rc<Term>; 37] {
    [
        &b.ty_nat,
        &b.ty_pi,
        &b.ty_ty,
        &b.ty_el,
        &b.ty_id,
        &b.ty_sigma,
        &b.ty_unit,
        &b.ty_empty,
        &b.tm_var,
        &b.tm_nat,
        &b.tm_pi,
        &b.tm_ty,
        &b.tm_zero,
        &b.tm_succ,
        &b.tm_elim_nat,
        &b.tm_lam,
        &b.tm_app,
        &b.tm_id,
        &b.tm_refl,
        &b.tm_j,
        &b.tm_sigma,
        &b.tm_pair,
        &b.tm_fst,
        &b.tm_snd,
        &b.tm_unit,
        &b.tm_empty,
        &b.tm_triv,
        &b.tm_elim_empty,
        &b.ty_sum,
        &b.tm_sum,
        &b.tm_inl,
        &b.tm_inr,
        &b.tm_case,
        &b.ty_w,
        &b.tm_w,
        &b.tm_sup,
        &b.tm_elim_w,
    ]
}

/// The 37 branch telescopes `G_Typ G_Trm` with their expected types, built
/// from the given motives (for conversion: the *left* side's, matching its
/// left-biased inference). `gamma` is the ambient local context (before any
/// telescope), used only for the shape of the identity substitutions in the
/// motive instantiations. The 13 ch. 04 branches come first in each group;
/// `ty_id`/`ty_sigma`/`ty_unit`/`ty_empty` and `tm_id`/`tm_refl`/`tm_j`/
/// `tm_sigma`/`tm_pair`/`tm_fst`/`tm_snd`/`tm_unit`/`tm_empty`/`tm_triv`/
/// `tm_elim_empty` plus the sum branches `ty_sum`/`tm_sum`/`tm_inl`/`tm_inr`/
/// `tm_case` and the W branches `ty_w`/`tm_w`/`tm_sup`/`tm_elim_w` are
/// extensions (kernel-v1-extensions).
pub(crate) fn branch_specs(
    motives: &Motives,
    l1: &Level,
    l2: &Level,
    gamma: &LocalCtx,
) -> [BranchSpec; 37] {
    let m_ty = &*motives.ty_motive;
    let m_tm = &*motives.tm_motive;
    let gt = |tu: u32, tg: u32| gamma.shift_univ(tu).shift_global(tg);

    // -- G_Typ --------------------------------------------------------------

    // (g. t_Nat) : M_Typ[0/ℓ, g/g, box Nat/x_T]
    let ty_nat = {
        let gt = gt(0, 1);
        BranchSpec {
            tele: Tele { univs: 0, globals: vec![GlobalBinding::Ctx], locals: vec![] },
            ty: Rc::new(inst_ty_motive(
                m_ty,
                (0, 1, 0),
                Level::Zero,
                g_ctx(0),
                Term::BoxTy(Rc::new(Type::Nat)),
                &gt,
            )),
            level: l1.clone(),
        }
    };

    // (ℓ, ℓ', g, U_S : Typ_c(g, ℓ), U_T : Typ_c((g, x : U_S^id @ ℓ), ℓ'),
    //  x_S, x_T. t_Π) : M_Typ[ℓ⊔ℓ'/ℓ, g/g, box (Π x:U_S^id. U_T^id)/x_T]
    let ty_pi = {
        let gt = gt(2, 3);
        // telescope view: g = 2, U_S = 1, U_T = 0
        let gx = ext_ctx(&g_ctx(2), gty(1, &g_ctx(2)), lvar(1));
        let x_s = inst_ty_motive(
            m_ty,
            (2, 3, 0),
            lvar(1),
            g_ctx(2),
            Term::BoxTy(Rc::new(gty(1, &g_ctx(2)))),
            &gt,
        );
        let x_t = inst_ty_motive(
            m_ty,
            (2, 3, 1),
            lvar(0),
            gx.clone(),
            Term::BoxTy(Rc::new(gty(0, &gx))),
            &gt,
        );
        let code = Type::Pi {
            dom_level: lvar(1),
            cod_level: lvar(0),
            dom: Rc::new(gty(1, &g_ctx(2))),
            cod: Rc::new(gty(0, &gx)),
        };
        BranchSpec {
            tele: Tele {
                univs: 2,
                globals: vec![
                    GlobalBinding::Ctx,
                    GlobalBinding::Ty { ctx: g_ctx(0), layer: Layer::Code, level: lvar(1) },
                    GlobalBinding::Ty {
                        ctx: ext_ctx(&g_ctx(1), gty(0, &g_ctx(1)), lvar(1)),
                        layer: Layer::Code,
                        level: lvar(0),
                    },
                ],
                locals: vec![
                    (Rc::new(x_s), l1.shift(2, 0)),
                    (Rc::new(x_t), l1.shift(2, 0)),
                ],
            },
            ty: Rc::new(inst_ty_motive(
                m_ty,
                (2, 3, 2),
                Level::max(lvar(1), lvar(0)),
                g_ctx(2),
                Term::BoxTy(Rc::new(code)),
                &gt,
            )),
            level: l1.shift(2, 0),
        }
    };

    // (ℓ, g. t_Ty) : M_Typ[1+ℓ/ℓ, g/g, box (Ty ℓ)/x_T]
    let ty_ty = {
        let gt = gt(1, 1);
        BranchSpec {
            tele: Tele { univs: 1, globals: vec![GlobalBinding::Ctx], locals: vec![] },
            ty: Rc::new(inst_ty_motive(
                m_ty,
                (1, 1, 0),
                Level::succ(lvar(0)),
                g_ctx(0),
                Term::BoxTy(Rc::new(Type::Ty(lvar(0)))),
                &gt,
            )),
            level: l1.shift(1, 0),
        }
    };

    // (ℓ, g, u_t : Trm_c(g ⊢ Ty ℓ @ 1+ℓ), x_t. t_El)
    //   : M_Typ[ℓ/ℓ, g/g, box (El ℓ u_t^id)/x_T]; x_t at the *term* motive
    let ty_el = {
        let gt = gt(1, 2);
        let x_t = inst_tm_motive(
            m_tm,
            (1, 2, 0),
            Level::succ(lvar(0)),
            g_ctx(1),
            Type::Ty(lvar(0)),
            Term::BoxTm(Rc::new(gtm(0, &g_ctx(1)))),
            &gt,
        );
        let code = Type::El { level: lvar(0), tm: Rc::new(gtm(0, &g_ctx(1))) };
        BranchSpec {
            tele: Tele {
                univs: 1,
                globals: vec![
                    GlobalBinding::Ctx,
                    GlobalBinding::Tm {
                        ctx: g_ctx(0),
                        layer: Layer::Code,
                        ty: Rc::new(Type::Ty(lvar(0))),
                        level: Level::succ(lvar(0)),
                    },
                ],
                locals: vec![(Rc::new(x_t), l2.shift(1, 0))],
            },
            ty: Rc::new(inst_ty_motive(
                m_ty,
                (1, 2, 1),
                lvar(0),
                g_ctx(1),
                Term::BoxTy(Rc::new(code)),
                &gt,
            )),
            level: l1.shift(1, 0),
        }
    };

    // (ℓ, g, U_S : Typ_c(g, ℓ), u_t : Trm_c(g ⊢ U_S^id @ ℓ),
    //  u_u : Trm_c(g ⊢ U_S^id @ ℓ), x_S, x_t, x_u. t_Id)
    //   : M_Typ[ℓ/ℓ, g/g, box (Id^ℓ(U_S^id; u_t^id; u_u^id))/x_T]
    // Extension beyond ch. 04 (kernel-v1-extensions).
    let ty_id = {
        let gt = gt(1, 4);
        // telescope view: g = 3, U_S = 2, u_t = 1, u_u = 0
        let x_s = inst_ty_motive(
            m_ty,
            (1, 4, 0),
            lvar(0),
            g_ctx(3),
            Term::BoxTy(Rc::new(gty(2, &g_ctx(3)))),
            &gt,
        );
        let x_t = inst_tm_motive(
            m_tm,
            (1, 4, 1),
            lvar(0),
            g_ctx(3),
            gty(2, &g_ctx(3)),
            Term::BoxTm(Rc::new(gtm(1, &g_ctx(3)))),
            &gt,
        );
        let x_u = inst_tm_motive(
            m_tm,
            (1, 4, 2),
            lvar(0),
            g_ctx(3),
            gty(2, &g_ctx(3)),
            Term::BoxTm(Rc::new(gtm(0, &g_ctx(3)))),
            &gt,
        );
        let code = Type::Id {
            level: lvar(0),
            ty: Rc::new(gty(2, &g_ctx(3))),
            lhs: Rc::new(gtm(1, &g_ctx(3))),
            rhs: Rc::new(gtm(0, &g_ctx(3))),
        };
        BranchSpec {
            tele: Tele {
                univs: 1,
                globals: vec![
                    GlobalBinding::Ctx,
                    GlobalBinding::Ty { ctx: g_ctx(0), layer: Layer::Code, level: lvar(0) },
                    GlobalBinding::Tm {
                        ctx: g_ctx(1),
                        layer: Layer::Code,
                        ty: Rc::new(gty(0, &g_ctx(1))),
                        level: lvar(0),
                    },
                    GlobalBinding::Tm {
                        ctx: g_ctx(2),
                        layer: Layer::Code,
                        ty: Rc::new(gty(1, &g_ctx(2))),
                        level: lvar(0),
                    },
                ],
                locals: vec![
                    (Rc::new(x_s), l1.shift(1, 0)),
                    (Rc::new(x_t), l2.shift(1, 0)),
                    (Rc::new(x_u), l2.shift(1, 0)),
                ],
            },
            ty: Rc::new(inst_ty_motive(
                m_ty,
                (1, 4, 3),
                lvar(0),
                g_ctx(3),
                Term::BoxTy(Rc::new(code)),
                &gt,
            )),
            level: l1.shift(1, 0),
        }
    };

    // (ℓ, ℓ', g, U_S : Typ_c(g, ℓ), U_T : Typ_c((g, x : U_S^id @ ℓ), ℓ'),
    //  x_S, x_T. t_Σ) : M_Typ[ℓ⊔ℓ'/ℓ, g/g, box (Σ x:U_S^id. U_T^id)/x_T]
    // Extension beyond ch. 04 (kernel-v1-extensions); mirrors ty_pi.
    let ty_sigma = {
        let gt = gt(2, 3);
        // telescope view: g = 2, U_S = 1, U_T = 0
        let gx = ext_ctx(&g_ctx(2), gty(1, &g_ctx(2)), lvar(1));
        let x_s = inst_ty_motive(
            m_ty,
            (2, 3, 0),
            lvar(1),
            g_ctx(2),
            Term::BoxTy(Rc::new(gty(1, &g_ctx(2)))),
            &gt,
        );
        let x_t = inst_ty_motive(
            m_ty,
            (2, 3, 1),
            lvar(0),
            gx.clone(),
            Term::BoxTy(Rc::new(gty(0, &gx))),
            &gt,
        );
        let code = Type::Sigma {
            fst_level: lvar(1),
            snd_level: lvar(0),
            fst: Rc::new(gty(1, &g_ctx(2))),
            snd: Rc::new(gty(0, &gx)),
        };
        BranchSpec {
            tele: Tele {
                univs: 2,
                globals: vec![
                    GlobalBinding::Ctx,
                    GlobalBinding::Ty { ctx: g_ctx(0), layer: Layer::Code, level: lvar(1) },
                    GlobalBinding::Ty {
                        ctx: ext_ctx(&g_ctx(1), gty(0, &g_ctx(1)), lvar(1)),
                        layer: Layer::Code,
                        level: lvar(0),
                    },
                ],
                locals: vec![
                    (Rc::new(x_s), l1.shift(2, 0)),
                    (Rc::new(x_t), l1.shift(2, 0)),
                ],
            },
            ty: Rc::new(inst_ty_motive(
                m_ty,
                (2, 3, 2),
                Level::max(lvar(1), lvar(0)),
                g_ctx(2),
                Term::BoxTy(Rc::new(code)),
                &gt,
            )),
            level: l1.shift(2, 0),
        }
    };

    // (g. t_Unit) : M_Typ[0/ℓ, g/g, box Unit/x_T]   (extension; mirrors ty_nat)
    let ty_unit = {
        let gt = gt(0, 1);
        BranchSpec {
            tele: Tele { univs: 0, globals: vec![GlobalBinding::Ctx], locals: vec![] },
            ty: Rc::new(inst_ty_motive(
                m_ty,
                (0, 1, 0),
                Level::Zero,
                g_ctx(0),
                Term::BoxTy(Rc::new(Type::Unit)),
                &gt,
            )),
            level: l1.clone(),
        }
    };

    // (g. t_Empty) : M_Typ[0/ℓ, g/g, box Empty/x_T]   (extension; mirrors ty_nat)
    let ty_empty = {
        let gt = gt(0, 1);
        BranchSpec {
            tele: Tele { univs: 0, globals: vec![GlobalBinding::Ctx], locals: vec![] },
            ty: Rc::new(inst_ty_motive(
                m_ty,
                (0, 1, 0),
                Level::Zero,
                g_ctx(0),
                Term::BoxTy(Rc::new(Type::Empty)),
                &gt,
            )),
            level: l1.clone(),
        }
    };

    // -- G_Trm --------------------------------------------------------------

    // (ℓ, g, U_T : Typ_p(g, ℓ), u_x : Trm_v(g ⊢ U_T^id @ ℓ). t_x)
    //   : M_Trm[ℓ/ℓ, g/g, U_T^id/U_T, box u_x^id/x_t]
    let tm_var = {
        let gt = gt(1, 3);
        BranchSpec {
            tele: Tele {
                univs: 1,
                globals: vec![
                    GlobalBinding::Ctx,
                    GlobalBinding::Ty { ctx: g_ctx(0), layer: Layer::Prog, level: lvar(0) },
                    GlobalBinding::Tm {
                        ctx: g_ctx(1),
                        layer: Layer::Var,
                        ty: Rc::new(gty(0, &g_ctx(1))),
                        level: lvar(0),
                    },
                ],
                locals: vec![],
            },
            ty: Rc::new(inst_tm_motive(
                m_tm,
                (1, 3, 0),
                lvar(0),
                g_ctx(2),
                gty(1, &g_ctx(2)),
                Term::BoxTm(Rc::new(gtm(0, &g_ctx(2)))),
                &gt,
            )),
            level: l2.shift(1, 0),
        }
    };

    // (g. t'_Nat) : M_Trm[1/ℓ, g/g, Ty 0/U_T, box Nat/x_t]
    let tm_nat = {
        let gt = gt(0, 1);
        BranchSpec {
            tele: Tele { univs: 0, globals: vec![GlobalBinding::Ctx], locals: vec![] },
            ty: Rc::new(inst_tm_motive(
                m_tm,
                (0, 1, 0),
                Level::constant(1),
                g_ctx(0),
                Type::Ty(Level::Zero),
                Term::BoxTm(Rc::new(Term::TmNat)),
                &gt,
            )),
            level: l2.clone(),
        }
    };

    // (ℓ, ℓ', g, u_s : Trm_c(g ⊢ Ty ℓ @ 1+ℓ),
    //  u_t : Trm_c((g, x : El ℓ u_s^id @ ℓ) ⊢ Ty ℓ' @ 1+ℓ'), x_s, x_t. t'_Π)
    //   : M_Trm[1+(ℓ⊔ℓ')/ℓ, g/g, Ty (ℓ⊔ℓ')/U_T, box (Π x:u_s^id. u_t^id)/x_t]
    let tm_pi = {
        let gt = gt(2, 3);
        // telescope view: g = 2, u_s = 1, u_t = 0
        let gx = ext_ctx(
            &g_ctx(2),
            Type::El { level: lvar(1), tm: Rc::new(gtm(1, &g_ctx(2))) },
            lvar(1),
        );
        let x_s = inst_tm_motive(
            m_tm,
            (2, 3, 0),
            Level::succ(lvar(1)),
            g_ctx(2),
            Type::Ty(lvar(1)),
            Term::BoxTm(Rc::new(gtm(1, &g_ctx(2)))),
            &gt,
        );
        let x_t = inst_tm_motive(
            m_tm,
            (2, 3, 1),
            Level::succ(lvar(0)),
            gx.clone(),
            Type::Ty(lvar(0)),
            Term::BoxTm(Rc::new(gtm(0, &gx))),
            &gt,
        );
        let lmax = Level::max(lvar(1), lvar(0));
        let code = Term::TmPi {
            dom_level: lvar(1),
            cod_level: lvar(0),
            dom: Rc::new(gtm(1, &g_ctx(2))),
            cod: Rc::new(gtm(0, &gx)),
        };
        BranchSpec {
            tele: Tele {
                univs: 2,
                globals: vec![
                    GlobalBinding::Ctx,
                    GlobalBinding::Tm {
                        ctx: g_ctx(0),
                        layer: Layer::Code,
                        ty: Rc::new(Type::Ty(lvar(1))),
                        level: Level::succ(lvar(1)),
                    },
                    GlobalBinding::Tm {
                        ctx: ext_ctx(
                            &g_ctx(1),
                            Type::El { level: lvar(1), tm: Rc::new(gtm(0, &g_ctx(1))) },
                            lvar(1),
                        ),
                        layer: Layer::Code,
                        ty: Rc::new(Type::Ty(lvar(0))),
                        level: Level::succ(lvar(0)),
                    },
                ],
                locals: vec![
                    (Rc::new(x_s), l2.shift(2, 0)),
                    (Rc::new(x_t), l2.shift(2, 0)),
                ],
            },
            ty: Rc::new(inst_tm_motive(
                m_tm,
                (2, 3, 2),
                Level::succ(lmax.clone()),
                g_ctx(2),
                Type::Ty(lmax),
                Term::BoxTm(Rc::new(code)),
                &gt,
            )),
            level: l2.shift(2, 0),
        }
    };

    // (ℓ, g. t'_Ty) : M_Trm[2+ℓ/ℓ, g/g, Ty (1+ℓ)/U_T, box (Ty ℓ)/x_t]
    let tm_ty = {
        let gt = gt(1, 1);
        BranchSpec {
            tele: Tele { univs: 1, globals: vec![GlobalBinding::Ctx], locals: vec![] },
            ty: Rc::new(inst_tm_motive(
                m_tm,
                (1, 1, 0),
                Level::succ(Level::succ(lvar(0))),
                g_ctx(0),
                Type::Ty(Level::succ(lvar(0))),
                Term::BoxTm(Rc::new(Term::TmTy(lvar(0)))),
                &gt,
            )),
            level: l2.shift(1, 0),
        }
    };

    // (g. t_ze) : M_Trm[0/ℓ, g/g, Nat/U_T, box ze/x_t]
    let tm_zero = {
        let gt = gt(0, 1);
        BranchSpec {
            tele: Tele { univs: 0, globals: vec![GlobalBinding::Ctx], locals: vec![] },
            ty: Rc::new(inst_tm_motive(
                m_tm,
                (0, 1, 0),
                Level::Zero,
                g_ctx(0),
                Type::Nat,
                Term::BoxTm(Rc::new(Term::Zero)),
                &gt,
            )),
            level: l2.clone(),
        }
    };

    // (g, u_t : Trm_c(g ⊢ Nat @ 0), x_t. t_succ)
    //   : M_Trm[0/ℓ, g/g, Nat/U_T, box (su u_t^id)/x_t]
    let tm_succ = {
        let gt = gt(0, 2);
        let x_t = inst_tm_motive(
            m_tm,
            (0, 2, 0),
            Level::Zero,
            g_ctx(1),
            Type::Nat,
            Term::BoxTm(Rc::new(gtm(0, &g_ctx(1)))),
            &gt,
        );
        let code = Term::Succ(Rc::new(gtm(0, &g_ctx(1))));
        BranchSpec {
            tele: Tele {
                univs: 0,
                globals: vec![
                    GlobalBinding::Ctx,
                    GlobalBinding::Tm {
                        ctx: g_ctx(0),
                        layer: Layer::Code,
                        ty: Rc::new(Type::Nat),
                        level: Level::Zero,
                    },
                ],
                locals: vec![(Rc::new(x_t), l2.clone())],
            },
            ty: Rc::new(inst_tm_motive(
                m_tm,
                (0, 2, 1),
                Level::Zero,
                g_ctx(1),
                Type::Nat,
                Term::BoxTm(Rc::new(code)),
                &gt,
            )),
            level: l2.clone(),
        }
    };

    // (ℓ, g, U_M : Typ_c((g, x : Nat @ 0), ℓ),
    //  u_s : Trm_c(g ⊢ U_M^{id,ze/x} @ ℓ),
    //  u_s' : Trm_c((g, x : Nat, y : U_M^id @ ℓ) ⊢ U_M^{id,su x/x} @ ℓ),
    //  u_t : Trm_c(g ⊢ Nat @ 0), x_M, x_s, x_s', x_t. t_elimN)
    //   : M_Trm[ℓ/ℓ, g/g, U_M^{id,u_t^id/x}/U_T, box (elim_Nat …)/x_t]
    let tm_elim_nat = {
        let gt = gt(1, 5);
        // telescope view: g = 4, U_M = 3, u_s = 2, u_s' = 1, u_t = 0
        let gx = ext_ctx(&g_ctx(4), Type::Nat, Level::Zero);
        let motive_code = Type::GlobalTy { var: GlobalVar(3), subst: LocalSubst::id(&gx) };
        let gxy = ext_ctx(&gx, motive_code.clone(), lvar(0));
        let x_m = inst_ty_motive(
            m_ty,
            (1, 5, 0),
            lvar(0),
            gx.clone(),
            Term::BoxTy(Rc::new(motive_code.clone())),
            &gt,
        );
        let u_m_at_zero = Type::GlobalTy {
            var: GlobalVar(3),
            subst: LocalSubst::id(&g_ctx(4)).extended(Rc::new(Term::Zero)),
        };
        let x_s = inst_tm_motive(
            m_tm,
            (1, 5, 1),
            lvar(0),
            g_ctx(4),
            u_m_at_zero,
            Term::BoxTm(Rc::new(gtm(2, &g_ctx(4)))),
            &gt,
        );
        let u_m_at_succ = Type::GlobalTy {
            var: GlobalVar(3),
            subst: LocalSubst::id(&g_ctx(4))
                .shift_local(2)
                .extended(Rc::new(Term::Succ(Rc::new(Term::Var(LocalVar(1)))))),
        };
        let x_s2 = inst_tm_motive(
            m_tm,
            (1, 5, 2),
            lvar(0),
            gxy.clone(),
            u_m_at_succ,
            Term::BoxTm(Rc::new(gtm(1, &gxy))),
            &gt,
        );
        let x_t = inst_tm_motive(
            m_tm,
            (1, 5, 3),
            lvar(0),
            g_ctx(4),
            Type::Nat,
            Term::BoxTm(Rc::new(gtm(0, &g_ctx(4)))),
            &gt,
        );
        let code = Term::ElimNat {
            level: lvar(0),
            motive: Rc::new(motive_code),
            base: Rc::new(gtm(2, &g_ctx(4))),
            step: Rc::new(gtm(1, &gxy)),
            scrut: Rc::new(gtm(0, &g_ctx(4))),
        };
        let u_m_at_scrut = Type::GlobalTy {
            var: GlobalVar(3),
            subst: LocalSubst::id(&g_ctx(4)).extended(Rc::new(gtm(0, &g_ctx(4)))),
        };
        BranchSpec {
            tele: Tele {
                univs: 1,
                globals: vec![
                    GlobalBinding::Ctx,
                    GlobalBinding::Ty {
                        ctx: ext_ctx(&g_ctx(0), Type::Nat, Level::Zero),
                        layer: Layer::Code,
                        level: lvar(0),
                    },
                    GlobalBinding::Tm {
                        ctx: g_ctx(1),
                        layer: Layer::Code,
                        ty: Rc::new(Type::GlobalTy {
                            var: GlobalVar(0),
                            subst: LocalSubst::id(&g_ctx(1)).extended(Rc::new(Term::Zero)),
                        }),
                        level: lvar(0),
                    },
                    GlobalBinding::Tm {
                        ctx: {
                            let gx = ext_ctx(&g_ctx(2), Type::Nat, Level::Zero);
                            let y_ty = Type::GlobalTy {
                                var: GlobalVar(1),
                                subst: LocalSubst::id(&gx),
                            };
                            ext_ctx(&gx, y_ty, lvar(0))
                        },
                        layer: Layer::Code,
                        ty: Rc::new(Type::GlobalTy {
                            var: GlobalVar(1),
                            subst: LocalSubst::id(&g_ctx(2))
                                .shift_local(2)
                                .extended(Rc::new(Term::Succ(Rc::new(Term::Var(
                                    LocalVar(1),
                                ))))),
                        }),
                        level: lvar(0),
                    },
                    GlobalBinding::Tm {
                        ctx: g_ctx(3),
                        layer: Layer::Code,
                        ty: Rc::new(Type::Nat),
                        level: Level::Zero,
                    },
                ],
                locals: vec![
                    (Rc::new(x_m), l1.shift(1, 0)),
                    (Rc::new(x_s), l2.shift(1, 0)),
                    (Rc::new(x_s2), l2.shift(1, 0)),
                    (Rc::new(x_t), l2.shift(1, 0)),
                ],
            },
            ty: Rc::new(inst_tm_motive(
                m_tm,
                (1, 5, 4),
                lvar(0),
                g_ctx(4),
                u_m_at_scrut,
                Term::BoxTm(Rc::new(code)),
                &gt,
            )),
            level: l2.shift(1, 0),
        }
    };

    // (ℓ, ℓ', g, U_S : Typ_c(g, ℓ), U_T : Typ_p((g, x : U_S^id @ ℓ), ℓ'),
    //  u_t : Trm_c((g, x : U_S^id @ ℓ) ⊢ U_T^id @ ℓ'), x_S, x_t. t_λ)
    //   : M_Trm[ℓ⊔ℓ'/ℓ, g/g, (Π x:U_S^id. U_T^id)/U_T, box (λ x:U_S^id. u_t^id)/x_t]
    // U_T is layer p (not a sub-structure of λ) — no recursive call.
    let tm_lam = {
        let gt = gt(2, 4);
        // telescope view: g = 3, U_S = 2, U_T = 1, u_t = 0
        let gx = ext_ctx(&g_ctx(3), gty(2, &g_ctx(3)), lvar(1));
        let x_s = inst_ty_motive(
            m_ty,
            (2, 4, 0),
            lvar(1),
            g_ctx(3),
            Term::BoxTy(Rc::new(gty(2, &g_ctx(3)))),
            &gt,
        );
        let x_t = inst_tm_motive(
            m_tm,
            (2, 4, 1),
            lvar(0),
            gx.clone(),
            gty(1, &gx),
            Term::BoxTm(Rc::new(gtm(0, &gx))),
            &gt,
        );
        let pi = Type::Pi {
            dom_level: lvar(1),
            cod_level: lvar(0),
            dom: Rc::new(gty(2, &g_ctx(3))),
            cod: Rc::new(gty(1, &gx)),
        };
        let code = Term::Lam {
            dom_level: lvar(1),
            cod_level: lvar(0),
            dom: Rc::new(gty(2, &g_ctx(3))),
            body: Rc::new(gtm(0, &gx)),
        };
        BranchSpec {
            tele: Tele {
                univs: 2,
                globals: vec![
                    GlobalBinding::Ctx,
                    GlobalBinding::Ty { ctx: g_ctx(0), layer: Layer::Code, level: lvar(1) },
                    GlobalBinding::Ty {
                        ctx: ext_ctx(&g_ctx(1), gty(0, &g_ctx(1)), lvar(1)),
                        layer: Layer::Prog,
                        level: lvar(0),
                    },
                    GlobalBinding::Tm {
                        ctx: ext_ctx(&g_ctx(2), gty(1, &g_ctx(2)), lvar(1)),
                        layer: Layer::Code,
                        ty: Rc::new(gty(
                            0,
                            &ext_ctx(&g_ctx(2), gty(1, &g_ctx(2)), lvar(1)),
                        )),
                        level: lvar(0),
                    },
                ],
                locals: vec![
                    (Rc::new(x_s), l1.shift(2, 0)),
                    (Rc::new(x_t), l2.shift(2, 0)),
                ],
            },
            ty: Rc::new(inst_tm_motive(
                m_tm,
                (2, 4, 2),
                Level::max(lvar(1), lvar(0)),
                g_ctx(3),
                pi,
                Term::BoxTm(Rc::new(code)),
                &gt,
            )),
            level: l2.shift(2, 0),
        }
    };

    // (ℓ, ℓ', g, U_S : Typ_c(g, ℓ), U_T : Typ_c((g, x : U_S^id @ ℓ), ℓ'),
    //  u_t : Trm_c(g ⊢ Π x:U_S^id. U_T^id @ ℓ⊔ℓ'), u_s : Trm_c(g ⊢ U_S^id @ ℓ),
    //  x_S, x_T, x_t, x_s. t_app)
    //   : M_Trm[ℓ'/ℓ, g/g, U_T^{id,u_s^id/x}/U_T, box (app(u_t^id; …; u_s^id))/x_t]
    // (the tex substitutes u_t^id for x here — a typo for u_s^id).
    let tm_app = {
        let gt = gt(2, 5);
        let u_t_pi = Type::Pi {
            dom_level: lvar(1),
            cod_level: lvar(0),
            dom: Rc::new(gty(1, &g_ctx(2))),
            cod: Rc::new(gty(0, &ext_ctx(&g_ctx(2), gty(1, &g_ctx(2)), lvar(1)))),
        };
        // telescope view: g = 4, U_S = 3, U_T = 2, u_t = 1, u_s = 0
        let gx = ext_ctx(&g_ctx(4), gty(3, &g_ctx(4)), lvar(1));
        let x_s = inst_ty_motive(
            m_ty,
            (2, 5, 0),
            lvar(1),
            g_ctx(4),
            Term::BoxTy(Rc::new(gty(3, &g_ctx(4)))),
            &gt,
        );
        let x_t_ty = inst_ty_motive(
            m_ty,
            (2, 5, 1),
            lvar(0),
            gx.clone(),
            Term::BoxTy(Rc::new(gty(2, &gx))),
            &gt,
        );
        let pi = Type::Pi {
            dom_level: lvar(1),
            cod_level: lvar(0),
            dom: Rc::new(gty(3, &g_ctx(4))),
            cod: Rc::new(gty(2, &gx)),
        };
        let x_t = inst_tm_motive(
            m_tm,
            (2, 5, 2),
            Level::max(lvar(1), lvar(0)),
            g_ctx(4),
            pi.clone(),
            Term::BoxTm(Rc::new(gtm(1, &g_ctx(4)))),
            &gt,
        );
        let x_s_tm = inst_tm_motive(
            m_tm,
            (2, 5, 3),
            lvar(1),
            g_ctx(4),
            gty(3, &g_ctx(4)),
            Term::BoxTm(Rc::new(gtm(0, &g_ctx(4)))),
            &gt,
        );
        let code = Term::App {
            fun: Rc::new(gtm(1, &g_ctx(4))),
            dom_level: lvar(1),
            cod_level: lvar(0),
            dom: Rc::new(gty(3, &g_ctx(4))),
            cod: Rc::new(gty(2, &gx)),
            arg: Rc::new(gtm(0, &g_ctx(4))),
        };
        let u_t_at_arg = Type::GlobalTy {
            var: GlobalVar(2),
            subst: LocalSubst::id(&g_ctx(4)).extended(Rc::new(gtm(0, &g_ctx(4)))),
        };
        BranchSpec {
            tele: Tele {
                univs: 2,
                globals: vec![
                    GlobalBinding::Ctx,
                    GlobalBinding::Ty { ctx: g_ctx(0), layer: Layer::Code, level: lvar(1) },
                    GlobalBinding::Ty {
                        ctx: ext_ctx(&g_ctx(1), gty(0, &g_ctx(1)), lvar(1)),
                        layer: Layer::Code,
                        level: lvar(0),
                    },
                    GlobalBinding::Tm {
                        ctx: g_ctx(2),
                        layer: Layer::Code,
                        ty: Rc::new(u_t_pi),
                        level: Level::max(lvar(1), lvar(0)),
                    },
                    GlobalBinding::Tm {
                        ctx: g_ctx(3),
                        layer: Layer::Code,
                        ty: Rc::new(gty(2, &g_ctx(3))),
                        level: lvar(1),
                    },
                ],
                locals: vec![
                    (Rc::new(x_s), l1.shift(2, 0)),
                    (Rc::new(x_t_ty), l1.shift(2, 0)),
                    (Rc::new(x_t), l2.shift(2, 0)),
                    (Rc::new(x_s_tm), l2.shift(2, 0)),
                ],
            },
            ty: Rc::new(inst_tm_motive(
                m_tm,
                (2, 5, 4),
                lvar(0),
                g_ctx(4),
                u_t_at_arg,
                Term::BoxTm(Rc::new(code)),
                &gt,
            )),
            level: l2.shift(2, 0),
        }
    };

    // -- extension branches (kernel-v1-extensions) --------------------------

    // (ℓ, g, u_S : Trm_c(g ⊢ Ty ℓ @ 1+ℓ), u_t : Trm_c(g ⊢ El ℓ u_S^id @ ℓ),
    //  u_u : Trm_c(g ⊢ El ℓ u_S^id @ ℓ), x_S, x_t, x_u. t'_Id)
    //   : M_Trm[1+ℓ/ℓ, g/g, Ty ℓ/U_T, box (Id^ℓ(u_S^id; u_t^id; u_u^id))/x_t]
    let tm_id = {
        let gt = gt(1, 4);
        // telescope view: g = 3, u_S = 2, u_t = 1, u_u = 0
        let el_s = Type::El { level: lvar(0), tm: Rc::new(gtm(2, &g_ctx(3))) };
        let x_s = inst_tm_motive(
            m_tm,
            (1, 4, 0),
            Level::succ(lvar(0)),
            g_ctx(3),
            Type::Ty(lvar(0)),
            Term::BoxTm(Rc::new(gtm(2, &g_ctx(3)))),
            &gt,
        );
        let x_t = inst_tm_motive(
            m_tm,
            (1, 4, 1),
            lvar(0),
            g_ctx(3),
            el_s.clone(),
            Term::BoxTm(Rc::new(gtm(1, &g_ctx(3)))),
            &gt,
        );
        let x_u = inst_tm_motive(
            m_tm,
            (1, 4, 2),
            lvar(0),
            g_ctx(3),
            el_s,
            Term::BoxTm(Rc::new(gtm(0, &g_ctx(3)))),
            &gt,
        );
        let code = Term::TmId {
            level: lvar(0),
            ty: Rc::new(gtm(2, &g_ctx(3))),
            lhs: Rc::new(gtm(1, &g_ctx(3))),
            rhs: Rc::new(gtm(0, &g_ctx(3))),
        };
        BranchSpec {
            tele: Tele {
                univs: 1,
                globals: vec![
                    GlobalBinding::Ctx,
                    GlobalBinding::Tm {
                        ctx: g_ctx(0),
                        layer: Layer::Code,
                        ty: Rc::new(Type::Ty(lvar(0))),
                        level: Level::succ(lvar(0)),
                    },
                    GlobalBinding::Tm {
                        ctx: g_ctx(1),
                        layer: Layer::Code,
                        ty: Rc::new(Type::El {
                            level: lvar(0),
                            tm: Rc::new(gtm(0, &g_ctx(1))),
                        }),
                        level: lvar(0),
                    },
                    GlobalBinding::Tm {
                        ctx: g_ctx(2),
                        layer: Layer::Code,
                        ty: Rc::new(Type::El {
                            level: lvar(0),
                            tm: Rc::new(gtm(1, &g_ctx(2))),
                        }),
                        level: lvar(0),
                    },
                ],
                locals: vec![
                    (Rc::new(x_s), l2.shift(1, 0)),
                    (Rc::new(x_t), l2.shift(1, 0)),
                    (Rc::new(x_u), l2.shift(1, 0)),
                ],
            },
            ty: Rc::new(inst_tm_motive(
                m_tm,
                (1, 4, 3),
                Level::succ(lvar(0)),
                g_ctx(3),
                Type::Ty(lvar(0)),
                Term::BoxTm(Rc::new(code)),
                &gt,
            )),
            level: l2.shift(1, 0),
        }
    };

    // (ℓ, g, U_S : Typ_c(g, ℓ), u_t : Trm_c(g ⊢ U_S^id @ ℓ), x_S, x_t. t_refl)
    //   : M_Trm[ℓ/ℓ, g/g, Id^ℓ(U_S^id; u_t^id; u_t^id)/U_T,
    //           box (refl^ℓ(U_S^id; u_t^id))/x_t]
    let tm_refl = {
        let gt = gt(1, 3);
        // telescope view: g = 2, U_S = 1, u_t = 0
        let x_s = inst_ty_motive(
            m_ty,
            (1, 3, 0),
            lvar(0),
            g_ctx(2),
            Term::BoxTy(Rc::new(gty(1, &g_ctx(2)))),
            &gt,
        );
        let x_t = inst_tm_motive(
            m_tm,
            (1, 3, 1),
            lvar(0),
            g_ctx(2),
            gty(1, &g_ctx(2)),
            Term::BoxTm(Rc::new(gtm(0, &g_ctx(2)))),
            &gt,
        );
        let code = Term::Refl {
            level: lvar(0),
            ty: Rc::new(gty(1, &g_ctx(2))),
            tm: Rc::new(gtm(0, &g_ctx(2))),
        };
        let id_ty = Type::Id {
            level: lvar(0),
            ty: Rc::new(gty(1, &g_ctx(2))),
            lhs: Rc::new(gtm(0, &g_ctx(2))),
            rhs: Rc::new(gtm(0, &g_ctx(2))),
        };
        BranchSpec {
            tele: Tele {
                univs: 1,
                globals: vec![
                    GlobalBinding::Ctx,
                    GlobalBinding::Ty { ctx: g_ctx(0), layer: Layer::Code, level: lvar(0) },
                    GlobalBinding::Tm {
                        ctx: g_ctx(1),
                        layer: Layer::Code,
                        ty: Rc::new(gty(0, &g_ctx(1))),
                        level: lvar(0),
                    },
                ],
                locals: vec![
                    (Rc::new(x_s), l1.shift(1, 0)),
                    (Rc::new(x_t), l2.shift(1, 0)),
                ],
            },
            ty: Rc::new(inst_tm_motive(
                m_tm,
                (1, 3, 2),
                lvar(0),
                g_ctx(2),
                id_ty,
                Term::BoxTm(Rc::new(code)),
                &gt,
            )),
            level: l2.shift(1, 0),
        }
    };

    // (ℓ, ℓ', g, U_S : Typ_c(g, ℓ), u_a : Trm_c(g ⊢ U_S^id @ ℓ),
    //  U_M : Typ_c((g, y : U_S^id @ ℓ, p : Id^ℓ(U_S; u_a; y) @ ℓ), ℓ'),
    //  u_c : Trm_c(g ⊢ U_M^{id, u_a/y, refl/p} @ ℓ'),
    //  u_r : Trm_c(g ⊢ U_S^id @ ℓ),
    //  u_e : Trm_c(g ⊢ Id^ℓ(U_S^id; u_a^id; u_r^id) @ ℓ),
    //  x_S, x_a, x_M, x_c, x_r, x_e. t_J)
    //   : M_Trm[ℓ'/ℓ, g/g, U_M^{id, u_r/y, u_e/p}/U_T, box (J …)/x_t]
    let tm_j = {
        let gt = gt(2, 7);
        // telescope view: g = 6, U_S = 5, u_a = 4, U_M = 3, u_c = 2,
        // u_r = 1, u_e = 0
        let gy = ext_ctx(&g_ctx(6), gty(5, &g_ctx(6)), lvar(1));
        // p's type is scoped over (g, y): weaken U_S^id / u_a^id by one.
        let p_ty = Type::Id {
            level: lvar(1),
            ty: Rc::new(gty(5, &g_ctx(6)).shift_local(1)),
            lhs: Rc::new(gtm(4, &g_ctx(6)).shift_local(1)),
            rhs: Rc::new(Term::Var(LocalVar(0))),
        };
        let gyp = ext_ctx(&gy, p_ty, lvar(1));
        let motive_code = Type::GlobalTy { var: GlobalVar(3), subst: LocalSubst::id(&gyp) };
        let x_s = inst_ty_motive(
            m_ty,
            (2, 7, 0),
            lvar(1),
            g_ctx(6),
            Term::BoxTy(Rc::new(gty(5, &g_ctx(6)))),
            &gt,
        );
        let x_a = inst_tm_motive(
            m_tm,
            (2, 7, 1),
            lvar(1),
            g_ctx(6),
            gty(5, &g_ctx(6)),
            Term::BoxTm(Rc::new(gtm(4, &g_ctx(6)))),
            &gt,
        );
        let x_m = inst_ty_motive(
            m_ty,
            (2, 7, 2),
            lvar(0),
            gyp.clone(),
            Term::BoxTy(Rc::new(motive_code.clone())),
            &gt,
        );
        let refl_a = Term::Refl {
            level: lvar(1),
            ty: Rc::new(gty(5, &g_ctx(6))),
            tm: Rc::new(gtm(4, &g_ctx(6))),
        };
        let u_m_at_refl = Type::GlobalTy {
            var: GlobalVar(3),
            subst: LocalSubst::id(&g_ctx(6))
                .extended(Rc::new(gtm(4, &g_ctx(6))))
                .extended(Rc::new(refl_a)),
        };
        let x_c = inst_tm_motive(
            m_tm,
            (2, 7, 3),
            lvar(0),
            g_ctx(6),
            u_m_at_refl,
            Term::BoxTm(Rc::new(gtm(2, &g_ctx(6)))),
            &gt,
        );
        let x_r = inst_tm_motive(
            m_tm,
            (2, 7, 4),
            lvar(1),
            g_ctx(6),
            gty(5, &g_ctx(6)),
            Term::BoxTm(Rc::new(gtm(1, &g_ctx(6)))),
            &gt,
        );
        let id_a_r = Type::Id {
            level: lvar(1),
            ty: Rc::new(gty(5, &g_ctx(6))),
            lhs: Rc::new(gtm(4, &g_ctx(6))),
            rhs: Rc::new(gtm(1, &g_ctx(6))),
        };
        let x_e = inst_tm_motive(
            m_tm,
            (2, 7, 5),
            lvar(1),
            g_ctx(6),
            id_a_r,
            Term::BoxTm(Rc::new(gtm(0, &g_ctx(6)))),
            &gt,
        );
        let code = Term::J {
            ty_level: lvar(1),
            motive_level: lvar(0),
            ty: Rc::new(gty(5, &g_ctx(6))),
            lhs: Rc::new(gtm(4, &g_ctx(6))),
            motive: Rc::new(motive_code),
            case: Rc::new(gtm(2, &g_ctx(6))),
            rhs: Rc::new(gtm(1, &g_ctx(6))),
            proof: Rc::new(gtm(0, &g_ctx(6))),
        };
        let u_m_at_scrut = Type::GlobalTy {
            var: GlobalVar(3),
            subst: LocalSubst::id(&g_ctx(6))
                .extended(Rc::new(gtm(1, &g_ctx(6))))
                .extended(Rc::new(gtm(0, &g_ctx(6)))),
        };
        BranchSpec {
            tele: Tele {
                univs: 2,
                globals: vec![
                    GlobalBinding::Ctx,
                    GlobalBinding::Ty { ctx: g_ctx(0), layer: Layer::Code, level: lvar(1) },
                    GlobalBinding::Tm {
                        ctx: g_ctx(1),
                        layer: Layer::Code,
                        ty: Rc::new(gty(0, &g_ctx(1))),
                        level: lvar(1),
                    },
                    GlobalBinding::Ty {
                        ctx: {
                            let gy = ext_ctx(&g_ctx(2), gty(1, &g_ctx(2)), lvar(1));
                            let p_ty = Type::Id {
                                level: lvar(1),
                                ty: Rc::new(gty(1, &g_ctx(2)).shift_local(1)),
                                lhs: Rc::new(gtm(0, &g_ctx(2)).shift_local(1)),
                                rhs: Rc::new(Term::Var(LocalVar(0))),
                            };
                            ext_ctx(&gy, p_ty, lvar(1))
                        },
                        layer: Layer::Code,
                        level: lvar(0),
                    },
                    GlobalBinding::Tm {
                        ctx: g_ctx(3),
                        layer: Layer::Code,
                        ty: Rc::new(Type::GlobalTy {
                            var: GlobalVar(0),
                            subst: LocalSubst::id(&g_ctx(3))
                                .extended(Rc::new(gtm(1, &g_ctx(3))))
                                .extended(Rc::new(Term::Refl {
                                    level: lvar(1),
                                    ty: Rc::new(gty(2, &g_ctx(3))),
                                    tm: Rc::new(gtm(1, &g_ctx(3))),
                                })),
                        }),
                        level: lvar(0),
                    },
                    GlobalBinding::Tm {
                        ctx: g_ctx(4),
                        layer: Layer::Code,
                        ty: Rc::new(gty(3, &g_ctx(4))),
                        level: lvar(1),
                    },
                    GlobalBinding::Tm {
                        ctx: g_ctx(5),
                        layer: Layer::Code,
                        ty: Rc::new(Type::Id {
                            level: lvar(1),
                            ty: Rc::new(gty(4, &g_ctx(5))),
                            lhs: Rc::new(gtm(3, &g_ctx(5))),
                            rhs: Rc::new(gtm(0, &g_ctx(5))),
                        }),
                        level: lvar(1),
                    },
                ],
                locals: vec![
                    (Rc::new(x_s), l1.shift(2, 0)),
                    (Rc::new(x_a), l2.shift(2, 0)),
                    (Rc::new(x_m), l1.shift(2, 0)),
                    (Rc::new(x_c), l2.shift(2, 0)),
                    (Rc::new(x_r), l2.shift(2, 0)),
                    (Rc::new(x_e), l2.shift(2, 0)),
                ],
            },
            ty: Rc::new(inst_tm_motive(
                m_tm,
                (2, 7, 6),
                lvar(0),
                g_ctx(6),
                u_m_at_scrut,
                Term::BoxTm(Rc::new(code)),
                &gt,
            )),
            level: l2.shift(2, 0),
        }
    };

    // (ℓ, ℓ', g, u_s : Trm_c(g ⊢ Ty ℓ @ 1+ℓ),
    //  u_t : Trm_c((g, x : El ℓ u_s^id @ ℓ) ⊢ Ty ℓ' @ 1+ℓ'), x_s, x_t. t'_Σ)
    //   : M_Trm[1+(ℓ⊔ℓ')/ℓ, g/g, Ty (ℓ⊔ℓ')/U_T, box (Σ x:u_s^id. u_t^id)/x_t]
    // Extension; mirrors tm_pi.
    let tm_sigma = {
        let gt = gt(2, 3);
        // telescope view: g = 2, u_s = 1, u_t = 0
        let gx = ext_ctx(
            &g_ctx(2),
            Type::El { level: lvar(1), tm: Rc::new(gtm(1, &g_ctx(2))) },
            lvar(1),
        );
        let x_s = inst_tm_motive(
            m_tm,
            (2, 3, 0),
            Level::succ(lvar(1)),
            g_ctx(2),
            Type::Ty(lvar(1)),
            Term::BoxTm(Rc::new(gtm(1, &g_ctx(2)))),
            &gt,
        );
        let x_t = inst_tm_motive(
            m_tm,
            (2, 3, 1),
            Level::succ(lvar(0)),
            gx.clone(),
            Type::Ty(lvar(0)),
            Term::BoxTm(Rc::new(gtm(0, &gx))),
            &gt,
        );
        let lmax = Level::max(lvar(1), lvar(0));
        let code = Term::TmSigma {
            fst_level: lvar(1),
            snd_level: lvar(0),
            fst: Rc::new(gtm(1, &g_ctx(2))),
            snd: Rc::new(gtm(0, &gx)),
        };
        BranchSpec {
            tele: Tele {
                univs: 2,
                globals: vec![
                    GlobalBinding::Ctx,
                    GlobalBinding::Tm {
                        ctx: g_ctx(0),
                        layer: Layer::Code,
                        ty: Rc::new(Type::Ty(lvar(1))),
                        level: Level::succ(lvar(1)),
                    },
                    GlobalBinding::Tm {
                        ctx: ext_ctx(
                            &g_ctx(1),
                            Type::El { level: lvar(1), tm: Rc::new(gtm(0, &g_ctx(1))) },
                            lvar(1),
                        ),
                        layer: Layer::Code,
                        ty: Rc::new(Type::Ty(lvar(0))),
                        level: Level::succ(lvar(0)),
                    },
                ],
                locals: vec![
                    (Rc::new(x_s), l2.shift(2, 0)),
                    (Rc::new(x_t), l2.shift(2, 0)),
                ],
            },
            ty: Rc::new(inst_tm_motive(
                m_tm,
                (2, 3, 2),
                Level::succ(lmax.clone()),
                g_ctx(2),
                Type::Ty(lmax),
                Term::BoxTm(Rc::new(code)),
                &gt,
            )),
            level: l2.shift(2, 0),
        }
    };

    // (ℓ, ℓ', g, U_S : Typ_c(g, ℓ), U_T : Typ_c((g, x : U_S^id @ ℓ), ℓ'),
    //  u_a : Trm_c(g ⊢ U_S^id @ ℓ), u_b : Trm_c(g ⊢ U_T^{id,u_a/x} @ ℓ'),
    //  x_S, x_T, x_a, x_b. t_pair)
    //   : M_Trm[ℓ⊔ℓ'/ℓ, g/g, Σ x:U_S^id. U_T^id / U_T,
    //           box (pair(x:U_S^id. U_T^id; u_a^id; u_b^id))/x_t]
    // Both type annotations are sub-structures (like app); extension.
    let tm_pair = {
        let gt = gt(2, 5);
        // telescope view: g = 4, U_S = 3, U_T = 2, u_a = 1, u_b = 0
        let gx = ext_ctx(&g_ctx(4), gty(3, &g_ctx(4)), lvar(1));
        let x_s = inst_ty_motive(
            m_ty,
            (2, 5, 0),
            lvar(1),
            g_ctx(4),
            Term::BoxTy(Rc::new(gty(3, &g_ctx(4)))),
            &gt,
        );
        let x_t = inst_ty_motive(
            m_ty,
            (2, 5, 1),
            lvar(0),
            gx.clone(),
            Term::BoxTy(Rc::new(gty(2, &gx))),
            &gt,
        );
        let x_a = inst_tm_motive(
            m_tm,
            (2, 5, 2),
            lvar(1),
            g_ctx(4),
            gty(3, &g_ctx(4)),
            Term::BoxTm(Rc::new(gtm(1, &g_ctx(4)))),
            &gt,
        );
        let u_t_at_ua = Type::GlobalTy {
            var: GlobalVar(2),
            subst: LocalSubst::id(&g_ctx(4)).extended(Rc::new(gtm(1, &g_ctx(4)))),
        };
        let x_b = inst_tm_motive(
            m_tm,
            (2, 5, 3),
            lvar(0),
            g_ctx(4),
            u_t_at_ua,
            Term::BoxTm(Rc::new(gtm(0, &g_ctx(4)))),
            &gt,
        );
        let sigma = Type::Sigma {
            fst_level: lvar(1),
            snd_level: lvar(0),
            fst: Rc::new(gty(3, &g_ctx(4))),
            snd: Rc::new(gty(2, &gx)),
        };
        let code = Term::Pair {
            fst_level: lvar(1),
            snd_level: lvar(0),
            fst_ty: Rc::new(gty(3, &g_ctx(4))),
            snd_ty: Rc::new(gty(2, &gx)),
            fst: Rc::new(gtm(1, &g_ctx(4))),
            snd: Rc::new(gtm(0, &g_ctx(4))),
        };
        BranchSpec {
            tele: Tele {
                univs: 2,
                globals: vec![
                    GlobalBinding::Ctx,
                    GlobalBinding::Ty { ctx: g_ctx(0), layer: Layer::Code, level: lvar(1) },
                    GlobalBinding::Ty {
                        ctx: ext_ctx(&g_ctx(1), gty(0, &g_ctx(1)), lvar(1)),
                        layer: Layer::Code,
                        level: lvar(0),
                    },
                    GlobalBinding::Tm {
                        ctx: g_ctx(2),
                        layer: Layer::Code,
                        ty: Rc::new(gty(1, &g_ctx(2))),
                        level: lvar(1),
                    },
                    GlobalBinding::Tm {
                        ctx: g_ctx(3),
                        layer: Layer::Code,
                        ty: Rc::new(Type::GlobalTy {
                            var: GlobalVar(1),
                            subst: LocalSubst::id(&g_ctx(3))
                                .extended(Rc::new(gtm(0, &g_ctx(3)))),
                        }),
                        level: lvar(0),
                    },
                ],
                locals: vec![
                    (Rc::new(x_s), l1.shift(2, 0)),
                    (Rc::new(x_t), l1.shift(2, 0)),
                    (Rc::new(x_a), l2.shift(2, 0)),
                    (Rc::new(x_b), l2.shift(2, 0)),
                ],
            },
            ty: Rc::new(inst_tm_motive(
                m_tm,
                (2, 5, 4),
                Level::max(lvar(1), lvar(0)),
                g_ctx(4),
                sigma,
                Term::BoxTm(Rc::new(code)),
                &gt,
            )),
            level: l2.shift(2, 0),
        }
    };

    // (ℓ, ℓ', g, U_S : Typ_c(g, ℓ), U_T : Typ_c((g, x : U_S^id @ ℓ), ℓ'),
    //  u_p : Trm_c(g ⊢ Σ x:U_S^id. U_T^id @ ℓ⊔ℓ'), x_S, x_T, x_p. t_fst)
    //   : M_Trm[ℓ/ℓ, g/g, U_S^id/U_T, box (fst(x:U_S^id.U_T^id; u_p^id))/x_t]
    // Extension.
    let tm_fst = {
        let gt = gt(2, 4);
        // telescope view: g = 3, U_S = 2, U_T = 1, u_p = 0
        let gx = ext_ctx(&g_ctx(3), gty(2, &g_ctx(3)), lvar(1));
        let x_s = inst_ty_motive(
            m_ty,
            (2, 4, 0),
            lvar(1),
            g_ctx(3),
            Term::BoxTy(Rc::new(gty(2, &g_ctx(3)))),
            &gt,
        );
        let x_t = inst_ty_motive(
            m_ty,
            (2, 4, 1),
            lvar(0),
            gx.clone(),
            Term::BoxTy(Rc::new(gty(1, &gx))),
            &gt,
        );
        let sigma = Type::Sigma {
            fst_level: lvar(1),
            snd_level: lvar(0),
            fst: Rc::new(gty(2, &g_ctx(3))),
            snd: Rc::new(gty(1, &gx)),
        };
        let x_p = inst_tm_motive(
            m_tm,
            (2, 4, 2),
            Level::max(lvar(1), lvar(0)),
            g_ctx(3),
            sigma.clone(),
            Term::BoxTm(Rc::new(gtm(0, &g_ctx(3)))),
            &gt,
        );
        let code = Term::Fst {
            fst_level: lvar(1),
            snd_level: lvar(0),
            fst_ty: Rc::new(gty(2, &g_ctx(3))),
            snd_ty: Rc::new(gty(1, &gx)),
            pair: Rc::new(gtm(0, &g_ctx(3))),
        };
        // u_p's binding type, scoped over [g, U_S, U_T] (g=2, U_S=1, U_T=0).
        let sigma_up = Type::Sigma {
            fst_level: lvar(1),
            snd_level: lvar(0),
            fst: Rc::new(gty(1, &g_ctx(2))),
            snd: Rc::new(gty(0, &ext_ctx(&g_ctx(2), gty(1, &g_ctx(2)), lvar(1)))),
        };
        BranchSpec {
            tele: Tele {
                univs: 2,
                globals: vec![
                    GlobalBinding::Ctx,
                    GlobalBinding::Ty { ctx: g_ctx(0), layer: Layer::Code, level: lvar(1) },
                    GlobalBinding::Ty {
                        ctx: ext_ctx(&g_ctx(1), gty(0, &g_ctx(1)), lvar(1)),
                        layer: Layer::Code,
                        level: lvar(0),
                    },
                    GlobalBinding::Tm {
                        ctx: g_ctx(2),
                        layer: Layer::Code,
                        ty: Rc::new(sigma_up),
                        level: Level::max(lvar(1), lvar(0)),
                    },
                ],
                locals: vec![
                    (Rc::new(x_s), l1.shift(2, 0)),
                    (Rc::new(x_t), l1.shift(2, 0)),
                    (Rc::new(x_p), l2.shift(2, 0)),
                ],
            },
            ty: Rc::new(inst_tm_motive(
                m_tm,
                (2, 4, 3),
                lvar(1),
                g_ctx(3),
                gty(2, &g_ctx(3)),
                Term::BoxTm(Rc::new(code)),
                &gt,
            )),
            level: l2.shift(2, 0),
        }
    };

    // (ℓ, ℓ', g, U_S, U_T, u_p, x_S, x_T, x_p. t_snd) — telescope as tm_fst;
    //   : M_Trm[ℓ'/ℓ, g/g, U_T^{id, fst(u_p^id)/x}/U_T,
    //           box (snd(x:U_S^id.U_T^id; u_p^id))/x_t]. Extension.
    let tm_snd = {
        let gt = gt(2, 4);
        // telescope view: g = 3, U_S = 2, U_T = 1, u_p = 0
        let gx = ext_ctx(&g_ctx(3), gty(2, &g_ctx(3)), lvar(1));
        let x_s = inst_ty_motive(
            m_ty,
            (2, 4, 0),
            lvar(1),
            g_ctx(3),
            Term::BoxTy(Rc::new(gty(2, &g_ctx(3)))),
            &gt,
        );
        let x_t = inst_ty_motive(
            m_ty,
            (2, 4, 1),
            lvar(0),
            gx.clone(),
            Term::BoxTy(Rc::new(gty(1, &gx))),
            &gt,
        );
        let sigma = Type::Sigma {
            fst_level: lvar(1),
            snd_level: lvar(0),
            fst: Rc::new(gty(2, &g_ctx(3))),
            snd: Rc::new(gty(1, &gx)),
        };
        let x_p = inst_tm_motive(
            m_tm,
            (2, 4, 2),
            Level::max(lvar(1), lvar(0)),
            g_ctx(3),
            sigma.clone(),
            Term::BoxTm(Rc::new(gtm(0, &g_ctx(3)))),
            &gt,
        );
        let fst_code = Term::Fst {
            fst_level: lvar(1),
            snd_level: lvar(0),
            fst_ty: Rc::new(gty(2, &g_ctx(3))),
            snd_ty: Rc::new(gty(1, &gx)),
            pair: Rc::new(gtm(0, &g_ctx(3))),
        };
        let snd_code = Term::Snd {
            fst_level: lvar(1),
            snd_level: lvar(0),
            fst_ty: Rc::new(gty(2, &g_ctx(3))),
            snd_ty: Rc::new(gty(1, &gx)),
            pair: Rc::new(gtm(0, &g_ctx(3))),
        };
        let u_t_at_fst = Type::GlobalTy {
            var: GlobalVar(1),
            subst: LocalSubst::id(&g_ctx(3)).extended(Rc::new(fst_code)),
        };
        let sigma_up = Type::Sigma {
            fst_level: lvar(1),
            snd_level: lvar(0),
            fst: Rc::new(gty(1, &g_ctx(2))),
            snd: Rc::new(gty(0, &ext_ctx(&g_ctx(2), gty(1, &g_ctx(2)), lvar(1)))),
        };
        BranchSpec {
            tele: Tele {
                univs: 2,
                globals: vec![
                    GlobalBinding::Ctx,
                    GlobalBinding::Ty { ctx: g_ctx(0), layer: Layer::Code, level: lvar(1) },
                    GlobalBinding::Ty {
                        ctx: ext_ctx(&g_ctx(1), gty(0, &g_ctx(1)), lvar(1)),
                        layer: Layer::Code,
                        level: lvar(0),
                    },
                    GlobalBinding::Tm {
                        ctx: g_ctx(2),
                        layer: Layer::Code,
                        ty: Rc::new(sigma_up),
                        level: Level::max(lvar(1), lvar(0)),
                    },
                ],
                locals: vec![
                    (Rc::new(x_s), l1.shift(2, 0)),
                    (Rc::new(x_t), l1.shift(2, 0)),
                    (Rc::new(x_p), l2.shift(2, 0)),
                ],
            },
            ty: Rc::new(inst_tm_motive(
                m_tm,
                (2, 4, 3),
                lvar(0),
                g_ctx(3),
                u_t_at_fst,
                Term::BoxTm(Rc::new(snd_code)),
                &gt,
            )),
            level: l2.shift(2, 0),
        }
    };

    // (g. t'_Unit) : M_Trm[1/ℓ, g/g, Ty 0/U_T, box Unit/x_t]
    //   (extension; mirrors tm_nat — code of the encoding Unit : Ty 0)
    let tm_unit = {
        let gt = gt(0, 1);
        BranchSpec {
            tele: Tele { univs: 0, globals: vec![GlobalBinding::Ctx], locals: vec![] },
            ty: Rc::new(inst_tm_motive(
                m_tm,
                (0, 1, 0),
                Level::constant(1),
                g_ctx(0),
                Type::Ty(Level::Zero),
                Term::BoxTm(Rc::new(Term::TmUnit)),
                &gt,
            )),
            level: l2.clone(),
        }
    };

    // (g. t'_Empty) : M_Trm[1/ℓ, g/g, Ty 0/U_T, box Empty/x_t]
    //   (extension; mirrors tm_nat)
    let tm_empty = {
        let gt = gt(0, 1);
        BranchSpec {
            tele: Tele { univs: 0, globals: vec![GlobalBinding::Ctx], locals: vec![] },
            ty: Rc::new(inst_tm_motive(
                m_tm,
                (0, 1, 0),
                Level::constant(1),
                g_ctx(0),
                Type::Ty(Level::Zero),
                Term::BoxTm(Rc::new(Term::TmEmpty)),
                &gt,
            )),
            level: l2.clone(),
        }
    };

    // (g. t_triv) : M_Trm[0/ℓ, g/g, Unit/U_T, box ⟨⟩/x_t]
    //   (extension; mirrors tm_zero — code of the intro ⟨⟩ : Unit)
    let tm_triv = {
        let gt = gt(0, 1);
        BranchSpec {
            tele: Tele { univs: 0, globals: vec![GlobalBinding::Ctx], locals: vec![] },
            ty: Rc::new(inst_tm_motive(
                m_tm,
                (0, 1, 0),
                Level::Zero,
                g_ctx(0),
                Type::Unit,
                Term::BoxTm(Rc::new(Term::Triv)),
                &gt,
            )),
            level: l2.clone(),
        }
    };

    // (ℓ, g, U_M : Typ_c((g, x : Empty @ 0), ℓ), u_t : Trm_c(g ⊢ Empty @ 0),
    //  x_M, x_t. t_elimE)
    //   : M_Trm[ℓ/ℓ, g/g, U_M^{id, u_t^id/x}/U_T, box (elim_Empty …)/x_t]
    // Extension; mirrors tm_elim_nat minus the base/step branches.
    let tm_elim_empty = {
        let gt = gt(1, 3);
        // telescope view: g = 2, U_M = 1, u_t = 0
        let gx = ext_ctx(&g_ctx(2), Type::Empty, Level::Zero);
        let motive_code = Type::GlobalTy { var: GlobalVar(1), subst: LocalSubst::id(&gx) };
        let x_m = inst_ty_motive(
            m_ty,
            (1, 3, 0),
            lvar(0),
            gx.clone(),
            Term::BoxTy(Rc::new(motive_code.clone())),
            &gt,
        );
        let x_t = inst_tm_motive(
            m_tm,
            (1, 3, 1),
            lvar(0),
            g_ctx(2),
            Type::Empty,
            Term::BoxTm(Rc::new(gtm(0, &g_ctx(2)))),
            &gt,
        );
        let code = Term::ElimEmpty {
            level: lvar(0),
            motive: Rc::new(motive_code),
            scrut: Rc::new(gtm(0, &g_ctx(2))),
        };
        let u_m_at_scrut = Type::GlobalTy {
            var: GlobalVar(1),
            subst: LocalSubst::id(&g_ctx(2)).extended(Rc::new(gtm(0, &g_ctx(2)))),
        };
        BranchSpec {
            tele: Tele {
                univs: 1,
                globals: vec![
                    GlobalBinding::Ctx,
                    GlobalBinding::Ty {
                        ctx: ext_ctx(&g_ctx(0), Type::Empty, Level::Zero),
                        layer: Layer::Code,
                        level: lvar(0),
                    },
                    GlobalBinding::Tm {
                        ctx: g_ctx(1),
                        layer: Layer::Code,
                        ty: Rc::new(Type::Empty),
                        level: Level::Zero,
                    },
                ],
                locals: vec![
                    (Rc::new(x_m), l1.shift(1, 0)),
                    (Rc::new(x_t), l2.shift(1, 0)),
                ],
            },
            ty: Rc::new(inst_tm_motive(
                m_tm,
                (1, 3, 2),
                lvar(0),
                g_ctx(2),
                u_m_at_scrut,
                Term::BoxTm(Rc::new(code)),
                &gt,
            )),
            level: l2.shift(1, 0),
        }
    };

    // (ℓ, ℓ', g, U_A : Typ_c(g, ℓ), U_B : Typ_c(g, ℓ'), x_A, x_B. t_+)
    //   : M_Typ[ℓ⊔ℓ'/ℓ, g/g, box (U_A^id +^{ℓ,ℓ'} U_B^id)/x_T]
    // Extension (kernel-v1-extensions); mirrors ty_sigma minus the binder
    // extension (both summands live in g).
    let ty_sum = {
        let gt = gt(2, 3);
        // telescope view: g = 2, U_A = 1, U_B = 0
        let x_a = inst_ty_motive(
            m_ty,
            (2, 3, 0),
            lvar(1),
            g_ctx(2),
            Term::BoxTy(Rc::new(gty(1, &g_ctx(2)))),
            &gt,
        );
        let x_b = inst_ty_motive(
            m_ty,
            (2, 3, 1),
            lvar(0),
            g_ctx(2),
            Term::BoxTy(Rc::new(gty(0, &g_ctx(2)))),
            &gt,
        );
        let code = Type::Sum {
            lhs_level: lvar(1),
            rhs_level: lvar(0),
            lhs: Rc::new(gty(1, &g_ctx(2))),
            rhs: Rc::new(gty(0, &g_ctx(2))),
        };
        BranchSpec {
            tele: Tele {
                univs: 2,
                globals: vec![
                    GlobalBinding::Ctx,
                    GlobalBinding::Ty { ctx: g_ctx(0), layer: Layer::Code, level: lvar(1) },
                    GlobalBinding::Ty { ctx: g_ctx(1), layer: Layer::Code, level: lvar(0) },
                ],
                locals: vec![
                    (Rc::new(x_a), l1.shift(2, 0)),
                    (Rc::new(x_b), l1.shift(2, 0)),
                ],
            },
            ty: Rc::new(inst_ty_motive(
                m_ty,
                (2, 3, 2),
                Level::max(lvar(1), lvar(0)),
                g_ctx(2),
                Term::BoxTy(Rc::new(code)),
                &gt,
            )),
            level: l1.shift(2, 0),
        }
    };

    // (ℓ, ℓ', g, u_a : Trm_c(g ⊢ Ty ℓ), u_b : Trm_c(g ⊢ Ty ℓ'), x_a, x_b. t'_+)
    //   : M_Trm[ℓ⊔ℓ'/ℓ, g/g, Ty (ℓ⊔ℓ')/U_T, box (u_a +^{ℓ,ℓ'} u_b)/x_t]
    // Extension; mirrors tm_sigma minus the binder extension.
    let tm_sum = {
        let gt = gt(2, 3);
        // telescope view: g = 2, u_a = 1, u_b = 0
        let x_a = inst_tm_motive(
            m_tm,
            (2, 3, 0),
            Level::succ(lvar(1)),
            g_ctx(2),
            Type::Ty(lvar(1)),
            Term::BoxTm(Rc::new(gtm(1, &g_ctx(2)))),
            &gt,
        );
        let x_b = inst_tm_motive(
            m_tm,
            (2, 3, 1),
            Level::succ(lvar(0)),
            g_ctx(2),
            Type::Ty(lvar(0)),
            Term::BoxTm(Rc::new(gtm(0, &g_ctx(2)))),
            &gt,
        );
        let lmax = Level::max(lvar(1), lvar(0));
        let code = Term::TmSum {
            lhs_level: lvar(1),
            rhs_level: lvar(0),
            lhs: Rc::new(gtm(1, &g_ctx(2))),
            rhs: Rc::new(gtm(0, &g_ctx(2))),
        };
        BranchSpec {
            tele: Tele {
                univs: 2,
                globals: vec![
                    GlobalBinding::Ctx,
                    GlobalBinding::Tm {
                        ctx: g_ctx(0),
                        layer: Layer::Code,
                        ty: Rc::new(Type::Ty(lvar(1))),
                        level: Level::succ(lvar(1)),
                    },
                    GlobalBinding::Tm {
                        ctx: g_ctx(1),
                        layer: Layer::Code,
                        ty: Rc::new(Type::Ty(lvar(0))),
                        level: Level::succ(lvar(0)),
                    },
                ],
                locals: vec![
                    (Rc::new(x_a), l2.shift(2, 0)),
                    (Rc::new(x_b), l2.shift(2, 0)),
                ],
            },
            ty: Rc::new(inst_tm_motive(
                m_tm,
                (2, 3, 2),
                Level::succ(lmax.clone()),
                g_ctx(2),
                Type::Ty(lmax),
                Term::BoxTm(Rc::new(code)),
                &gt,
            )),
            level: l2.shift(2, 0),
        }
    };

    // (ℓ, ℓ', g, U_A : Typ_c(g, ℓ), U_B : Typ_c(g, ℓ'),
    //  u_a : Trm_c(g ⊢ U_A^id @ ℓ), x_A, x_B, x_a. t_inl)
    //   : M_Trm[ℓ⊔ℓ'/ℓ, g/g, (U_A^id + U_B^id)/U_T,
    //           box (inl(U_A^id; U_B^id; u_a^id))/x_t]. Extension.
    let tm_inl = {
        let gt = gt(2, 4);
        // telescope view: g = 3, U_A = 2, U_B = 1, u_a = 0
        let x_a_ty = inst_ty_motive(
            m_ty,
            (2, 4, 0),
            lvar(1),
            g_ctx(3),
            Term::BoxTy(Rc::new(gty(2, &g_ctx(3)))),
            &gt,
        );
        let x_b_ty = inst_ty_motive(
            m_ty,
            (2, 4, 1),
            lvar(0),
            g_ctx(3),
            Term::BoxTy(Rc::new(gty(1, &g_ctx(3)))),
            &gt,
        );
        let x_a = inst_tm_motive(
            m_tm,
            (2, 4, 2),
            lvar(1),
            g_ctx(3),
            gty(2, &g_ctx(3)),
            Term::BoxTm(Rc::new(gtm(0, &g_ctx(3)))),
            &gt,
        );
        let sum = Type::Sum {
            lhs_level: lvar(1),
            rhs_level: lvar(0),
            lhs: Rc::new(gty(2, &g_ctx(3))),
            rhs: Rc::new(gty(1, &g_ctx(3))),
        };
        let code = Term::Inl {
            lhs_level: lvar(1),
            rhs_level: lvar(0),
            lhs: Rc::new(gty(2, &g_ctx(3))),
            rhs: Rc::new(gty(1, &g_ctx(3))),
            val: Rc::new(gtm(0, &g_ctx(3))),
        };
        BranchSpec {
            tele: Tele {
                univs: 2,
                globals: vec![
                    GlobalBinding::Ctx,
                    GlobalBinding::Ty { ctx: g_ctx(0), layer: Layer::Code, level: lvar(1) },
                    GlobalBinding::Ty { ctx: g_ctx(1), layer: Layer::Code, level: lvar(0) },
                    GlobalBinding::Tm {
                        ctx: g_ctx(2),
                        layer: Layer::Code,
                        ty: Rc::new(gty(1, &g_ctx(2))),
                        level: lvar(1),
                    },
                ],
                locals: vec![
                    (Rc::new(x_a_ty), l1.shift(2, 0)),
                    (Rc::new(x_b_ty), l1.shift(2, 0)),
                    (Rc::new(x_a), l2.shift(2, 0)),
                ],
            },
            ty: Rc::new(inst_tm_motive(
                m_tm,
                (2, 4, 3),
                Level::max(lvar(1), lvar(0)),
                g_ctx(3),
                sum,
                Term::BoxTm(Rc::new(code)),
                &gt,
            )),
            level: l2.shift(2, 0),
        }
    };

    // (ℓ, ℓ', g, U_A, U_B, u_b : Trm_c(g ⊢ U_B^id @ ℓ'), x_A, x_B, x_b. t_inr)
    //   : M_Trm[ℓ⊔ℓ'/ℓ, g/g, (U_A^id + U_B^id)/U_T,
    //           box (inr(U_A^id; U_B^id; u_b^id))/x_t]. Extension.
    let tm_inr = {
        let gt = gt(2, 4);
        // telescope view: g = 3, U_A = 2, U_B = 1, u_b = 0
        let x_a_ty = inst_ty_motive(
            m_ty,
            (2, 4, 0),
            lvar(1),
            g_ctx(3),
            Term::BoxTy(Rc::new(gty(2, &g_ctx(3)))),
            &gt,
        );
        let x_b_ty = inst_ty_motive(
            m_ty,
            (2, 4, 1),
            lvar(0),
            g_ctx(3),
            Term::BoxTy(Rc::new(gty(1, &g_ctx(3)))),
            &gt,
        );
        let x_b = inst_tm_motive(
            m_tm,
            (2, 4, 2),
            lvar(0),
            g_ctx(3),
            gty(1, &g_ctx(3)),
            Term::BoxTm(Rc::new(gtm(0, &g_ctx(3)))),
            &gt,
        );
        let sum = Type::Sum {
            lhs_level: lvar(1),
            rhs_level: lvar(0),
            lhs: Rc::new(gty(2, &g_ctx(3))),
            rhs: Rc::new(gty(1, &g_ctx(3))),
        };
        let code = Term::Inr {
            lhs_level: lvar(1),
            rhs_level: lvar(0),
            lhs: Rc::new(gty(2, &g_ctx(3))),
            rhs: Rc::new(gty(1, &g_ctx(3))),
            val: Rc::new(gtm(0, &g_ctx(3))),
        };
        BranchSpec {
            tele: Tele {
                univs: 2,
                globals: vec![
                    GlobalBinding::Ctx,
                    GlobalBinding::Ty { ctx: g_ctx(0), layer: Layer::Code, level: lvar(1) },
                    GlobalBinding::Ty { ctx: g_ctx(1), layer: Layer::Code, level: lvar(0) },
                    GlobalBinding::Tm {
                        ctx: g_ctx(2),
                        layer: Layer::Code,
                        ty: Rc::new(gty(0, &g_ctx(2))),
                        level: lvar(0),
                    },
                ],
                locals: vec![
                    (Rc::new(x_a_ty), l1.shift(2, 0)),
                    (Rc::new(x_b_ty), l1.shift(2, 0)),
                    (Rc::new(x_b), l2.shift(2, 0)),
                ],
            },
            ty: Rc::new(inst_tm_motive(
                m_tm,
                (2, 4, 3),
                Level::max(lvar(1), lvar(0)),
                g_ctx(3),
                sum,
                Term::BoxTm(Rc::new(code)),
                &gt,
            )),
            level: l2.shift(2, 0),
        }
    };

    // (ℓ, ℓ', ℓ'', g, U_A : Typ_c(g, ℓ), U_B : Typ_c(g, ℓ'),
    //  U_M : Typ_c((g, z : (U_A^id + U_B^id) @ ℓ⊔ℓ'), ℓ''),
    //  u_l : Trm_c((g, x : U_A^id @ ℓ) ⊢ U_M^{id, inl x/z} @ ℓ''),
    //  u_r : Trm_c((g, y : U_B^id @ ℓ') ⊢ U_M^{id, inr y/z} @ ℓ''),
    //  u_t : Trm_c(g ⊢ (U_A^id + U_B^id) @ ℓ⊔ℓ'),
    //  x_A, x_B, x_M, x_l, x_r, x_t. t_case)
    //   : M_Trm[ℓ''/ℓ, g/g, U_M^{id, u_t^id/z}/U_T,
    //           box (case (z. U_M^id) (x. u_l^id) (y. u_r^id) u_t^id)/x_t]
    // A positive dependent eliminator (mirrors tm_elim_nat's shape).
    // Extension.
    let tm_case = {
        let gt = gt(3, 7);
        // telescope view: g = 6, U_A = 5, U_B = 4, U_M = 3, u_l = 2, u_r = 1,
        // u_t = 0. Univs: ℓ = lvar(2), ℓ' = lvar(1), ℓ'' = lvar(0).
        let lmax = Level::max(lvar(2), lvar(1));
        let sum6 = Type::Sum {
            lhs_level: lvar(2),
            rhs_level: lvar(1),
            lhs: Rc::new(gty(5, &g_ctx(6))),
            rhs: Rc::new(gty(4, &g_ctx(6))),
        };
        let gz = ext_ctx(&g_ctx(6), sum6.clone(), lmax.clone());
        let gx_a = ext_ctx(&g_ctx(6), gty(5, &g_ctx(6)), lvar(2));
        let gx_b = ext_ctx(&g_ctx(6), gty(4, &g_ctx(6)), lvar(1));
        // U_M^{id, inl x/z} and U_M^{id, inr y/z}, scoped in (g, x)/(g, y).
        let inl_x = Term::Inl {
            lhs_level: lvar(2),
            rhs_level: lvar(1),
            lhs: Rc::new(gty(5, &g_ctx(6)).shift_local(1)),
            rhs: Rc::new(gty(4, &g_ctx(6)).shift_local(1)),
            val: Rc::new(Term::Var(LocalVar(0))),
        };
        let inr_y = Term::Inr {
            lhs_level: lvar(2),
            rhs_level: lvar(1),
            lhs: Rc::new(gty(5, &g_ctx(6)).shift_local(1)),
            rhs: Rc::new(gty(4, &g_ctx(6)).shift_local(1)),
            val: Rc::new(Term::Var(LocalVar(0))),
        };
        let u_m_at_inl = Type::GlobalTy {
            var: GlobalVar(3),
            subst: LocalSubst::id(&g_ctx(6)).shift_local(1).extended(Rc::new(inl_x)),
        };
        let u_m_at_inr = Type::GlobalTy {
            var: GlobalVar(3),
            subst: LocalSubst::id(&g_ctx(6)).shift_local(1).extended(Rc::new(inr_y)),
        };
        let x_a = inst_ty_motive(
            m_ty,
            (3, 7, 0),
            lvar(2),
            g_ctx(6),
            Term::BoxTy(Rc::new(gty(5, &g_ctx(6)))),
            &gt,
        );
        let x_b = inst_ty_motive(
            m_ty,
            (3, 7, 1),
            lvar(1),
            g_ctx(6),
            Term::BoxTy(Rc::new(gty(4, &g_ctx(6)))),
            &gt,
        );
        let x_m = inst_ty_motive(
            m_ty,
            (3, 7, 2),
            lvar(0),
            gz.clone(),
            Term::BoxTy(Rc::new(gty(3, &gz))),
            &gt,
        );
        let x_l = inst_tm_motive(
            m_tm,
            (3, 7, 3),
            lvar(0),
            gx_a.clone(),
            u_m_at_inl.clone(),
            Term::BoxTm(Rc::new(gtm(2, &gx_a))),
            &gt,
        );
        let x_r = inst_tm_motive(
            m_tm,
            (3, 7, 4),
            lvar(0),
            gx_b.clone(),
            u_m_at_inr.clone(),
            Term::BoxTm(Rc::new(gtm(1, &gx_b))),
            &gt,
        );
        let x_t = inst_tm_motive(
            m_tm,
            (3, 7, 5),
            lmax.clone(),
            g_ctx(6),
            sum6.clone(),
            Term::BoxTm(Rc::new(gtm(0, &g_ctx(6)))),
            &gt,
        );
        let code = Term::Case {
            lhs_level: lvar(2),
            rhs_level: lvar(1),
            motive_level: lvar(0),
            lhs: Rc::new(gty(5, &g_ctx(6))),
            rhs: Rc::new(gty(4, &g_ctx(6))),
            motive: Rc::new(gty(3, &gz)),
            case_l: Rc::new(gtm(2, &gx_a)),
            case_r: Rc::new(gtm(1, &gx_b)),
            scrut: Rc::new(gtm(0, &g_ctx(6))),
        };
        // Result type U_M^{id, u_t^id/z}.
        let u_m_at_scrut = Type::GlobalTy {
            var: GlobalVar(3),
            subst: LocalSubst::id(&g_ctx(6)).extended(Rc::new(gtm(0, &g_ctx(6)))),
        };
        // -- global bindings, each scoped in its own Ψ-prefix --
        // U_M's context (g, z : sum), prefix (g, U_A, U_B): g=2, U_A=1, U_B=0.
        let sum_um = Type::Sum {
            lhs_level: lvar(2),
            rhs_level: lvar(1),
            lhs: Rc::new(gty(1, &g_ctx(2))),
            rhs: Rc::new(gty(0, &g_ctx(2))),
        };
        let gz_um = ext_ctx(&g_ctx(2), sum_um, lmax.clone());
        // u_l's binding, prefix (g, U_A, U_B, U_M): g=3, U_A=2, U_B=1, U_M=0.
        let inl_x_l = Term::Inl {
            lhs_level: lvar(2),
            rhs_level: lvar(1),
            lhs: Rc::new(gty(2, &g_ctx(3)).shift_local(1)),
            rhs: Rc::new(gty(1, &g_ctx(3)).shift_local(1)),
            val: Rc::new(Term::Var(LocalVar(0))),
        };
        let u_m_bind_l = Type::GlobalTy {
            var: GlobalVar(0),
            subst: LocalSubst::id(&g_ctx(3)).shift_local(1).extended(Rc::new(inl_x_l)),
        };
        // u_r's binding, prefix (g, U_A, U_B, U_M, u_l): g=4, U_A=3, U_B=2,
        // U_M=1.
        let inr_y_r = Term::Inr {
            lhs_level: lvar(2),
            rhs_level: lvar(1),
            lhs: Rc::new(gty(3, &g_ctx(4)).shift_local(1)),
            rhs: Rc::new(gty(2, &g_ctx(4)).shift_local(1)),
            val: Rc::new(Term::Var(LocalVar(0))),
        };
        let u_m_bind_r = Type::GlobalTy {
            var: GlobalVar(1),
            subst: LocalSubst::id(&g_ctx(4)).shift_local(1).extended(Rc::new(inr_y_r)),
        };
        // u_t's binding, prefix (g, U_A, U_B, U_M, u_l, u_r): g=5, U_A=4, U_B=3.
        let sum_ut = Type::Sum {
            lhs_level: lvar(2),
            rhs_level: lvar(1),
            lhs: Rc::new(gty(4, &g_ctx(5))),
            rhs: Rc::new(gty(3, &g_ctx(5))),
        };
        BranchSpec {
            tele: Tele {
                univs: 3,
                globals: vec![
                    GlobalBinding::Ctx,
                    GlobalBinding::Ty { ctx: g_ctx(0), layer: Layer::Code, level: lvar(2) },
                    GlobalBinding::Ty { ctx: g_ctx(1), layer: Layer::Code, level: lvar(1) },
                    GlobalBinding::Ty { ctx: gz_um, layer: Layer::Code, level: lvar(0) },
                    GlobalBinding::Tm {
                        ctx: ext_ctx(&g_ctx(3), gty(2, &g_ctx(3)), lvar(2)),
                        layer: Layer::Code,
                        ty: Rc::new(u_m_bind_l),
                        level: lvar(0),
                    },
                    GlobalBinding::Tm {
                        ctx: ext_ctx(&g_ctx(4), gty(2, &g_ctx(4)), lvar(1)),
                        layer: Layer::Code,
                        ty: Rc::new(u_m_bind_r),
                        level: lvar(0),
                    },
                    GlobalBinding::Tm {
                        ctx: g_ctx(5),
                        layer: Layer::Code,
                        ty: Rc::new(sum_ut),
                        level: lmax.clone(),
                    },
                ],
                locals: vec![
                    (Rc::new(x_a), l1.shift(3, 0)),
                    (Rc::new(x_b), l1.shift(3, 0)),
                    (Rc::new(x_m), l1.shift(3, 0)),
                    (Rc::new(x_l), l2.shift(3, 0)),
                    (Rc::new(x_r), l2.shift(3, 0)),
                    (Rc::new(x_t), l2.shift(3, 0)),
                ],
            },
            ty: Rc::new(inst_tm_motive(
                m_tm,
                (3, 7, 6),
                lvar(0),
                g_ctx(6),
                u_m_at_scrut,
                Term::BoxTm(Rc::new(code)),
                &gt,
            )),
            level: l2.shift(3, 0),
        }
    };

    // (ℓ, ℓ', g, U_S : Typ_c(g, ℓ), U_T : Typ_c((g, x : U_S^id @ ℓ), ℓ'),
    //  x_S, x_T. t_W) : M_Typ[ℓ⊔ℓ'/ℓ, g/g, box (W x:U_S^id. U_T^id)/x_T]
    // Extension (kernel-v1-extensions); mirrors ty_pi/ty_sigma.
    let ty_w = {
        let gt = gt(2, 3);
        // telescope view: g = 2, U_S = 1, U_T = 0
        let gx = ext_ctx(&g_ctx(2), gty(1, &g_ctx(2)), lvar(1));
        let x_s = inst_ty_motive(
            m_ty,
            (2, 3, 0),
            lvar(1),
            g_ctx(2),
            Term::BoxTy(Rc::new(gty(1, &g_ctx(2)))),
            &gt,
        );
        let x_t = inst_ty_motive(
            m_ty,
            (2, 3, 1),
            lvar(0),
            gx.clone(),
            Term::BoxTy(Rc::new(gty(0, &gx))),
            &gt,
        );
        let code = Type::W {
            shape_level: lvar(1),
            pos_level: lvar(0),
            shape: Rc::new(gty(1, &g_ctx(2))),
            pos: Rc::new(gty(0, &gx)),
        };
        BranchSpec {
            tele: Tele {
                univs: 2,
                globals: vec![
                    GlobalBinding::Ctx,
                    GlobalBinding::Ty { ctx: g_ctx(0), layer: Layer::Code, level: lvar(1) },
                    GlobalBinding::Ty {
                        ctx: ext_ctx(&g_ctx(1), gty(0, &g_ctx(1)), lvar(1)),
                        layer: Layer::Code,
                        level: lvar(0),
                    },
                ],
                locals: vec![
                    (Rc::new(x_s), l1.shift(2, 0)),
                    (Rc::new(x_t), l1.shift(2, 0)),
                ],
            },
            ty: Rc::new(inst_ty_motive(
                m_ty,
                (2, 3, 2),
                Level::max(lvar(1), lvar(0)),
                g_ctx(2),
                Term::BoxTy(Rc::new(code)),
                &gt,
            )),
            level: l1.shift(2, 0),
        }
    };

    // (ℓ, ℓ', g, u_s : Trm_c(g ⊢ Ty ℓ @ 1+ℓ),
    //  u_t : Trm_c((g, x : El ℓ u_s^id @ ℓ) ⊢ Ty ℓ' @ 1+ℓ'), x_s, x_t. t'_W)
    //   : M_Trm[1+(ℓ⊔ℓ')/ℓ, g/g, Ty (ℓ⊔ℓ')/U_T, box (W x:u_s^id. u_t^id)/x_t]
    // Extension; mirrors tm_pi/tm_sigma.
    let tm_w = {
        let gt = gt(2, 3);
        // telescope view: g = 2, u_s = 1, u_t = 0
        let gx = ext_ctx(
            &g_ctx(2),
            Type::El { level: lvar(1), tm: Rc::new(gtm(1, &g_ctx(2))) },
            lvar(1),
        );
        let x_s = inst_tm_motive(
            m_tm,
            (2, 3, 0),
            Level::succ(lvar(1)),
            g_ctx(2),
            Type::Ty(lvar(1)),
            Term::BoxTm(Rc::new(gtm(1, &g_ctx(2)))),
            &gt,
        );
        let x_t = inst_tm_motive(
            m_tm,
            (2, 3, 1),
            Level::succ(lvar(0)),
            gx.clone(),
            Type::Ty(lvar(0)),
            Term::BoxTm(Rc::new(gtm(0, &gx))),
            &gt,
        );
        let lmax = Level::max(lvar(1), lvar(0));
        let code = Term::TmW {
            shape_level: lvar(1),
            pos_level: lvar(0),
            shape: Rc::new(gtm(1, &g_ctx(2))),
            pos: Rc::new(gtm(0, &gx)),
        };
        BranchSpec {
            tele: Tele {
                univs: 2,
                globals: vec![
                    GlobalBinding::Ctx,
                    GlobalBinding::Tm {
                        ctx: g_ctx(0),
                        layer: Layer::Code,
                        ty: Rc::new(Type::Ty(lvar(1))),
                        level: Level::succ(lvar(1)),
                    },
                    GlobalBinding::Tm {
                        ctx: ext_ctx(
                            &g_ctx(1),
                            Type::El { level: lvar(1), tm: Rc::new(gtm(0, &g_ctx(1))) },
                            lvar(1),
                        ),
                        layer: Layer::Code,
                        ty: Rc::new(Type::Ty(lvar(0))),
                        level: Level::succ(lvar(0)),
                    },
                ],
                locals: vec![
                    (Rc::new(x_s), l2.shift(2, 0)),
                    (Rc::new(x_t), l2.shift(2, 0)),
                ],
            },
            ty: Rc::new(inst_tm_motive(
                m_tm,
                (2, 3, 2),
                Level::succ(lmax.clone()),
                g_ctx(2),
                Type::Ty(lmax),
                Term::BoxTm(Rc::new(code)),
                &gt,
            )),
            level: l2.shift(2, 0),
        }
    };

    // (ℓ, ℓ', g, U_S : Typ_c(g, ℓ), U_T : Typ_c((g, x : U_S^id @ ℓ), ℓ'),
    //  u_a : Trm_c(g ⊢ U_S^id @ ℓ),
    //  u_f : Trm_c(g ⊢ Π^{ℓ',ℓ⊔ℓ'}(y : U_T^{id,u_a/x}). W(x:U_S^id).U_T^id
    //        @ ℓ⊔ℓ'), x_S, x_T, x_a, x_f. t_sup)
    //   : M_Trm[ℓ⊔ℓ'/ℓ, g/g, W(x:U_S^id).U_T^id / U_T,
    //           box (sup(x:U_S^id. U_T^id; u_a^id; u_f^id))/x_t]
    // Both type annotations are sub-structures (like pair); extension.
    let tm_sup = {
        let gt = gt(2, 5);
        let lmax = Level::max(lvar(1), lvar(0));
        // telescope view: g = 4, U_S = 3, U_T = 2, u_a = 1, u_f = 0
        let gx = ext_ctx(&g_ctx(4), gty(3, &g_ctx(4)), lvar(1));
        let x_s = inst_ty_motive(
            m_ty,
            (2, 5, 0),
            lvar(1),
            g_ctx(4),
            Term::BoxTy(Rc::new(gty(3, &g_ctx(4)))),
            &gt,
        );
        let x_t = inst_ty_motive(
            m_ty,
            (2, 5, 1),
            lvar(0),
            gx.clone(),
            Term::BoxTy(Rc::new(gty(2, &gx))),
            &gt,
        );
        let x_a = inst_tm_motive(
            m_tm,
            (2, 5, 2),
            lvar(1),
            g_ctx(4),
            gty(3, &g_ctx(4)),
            Term::BoxTm(Rc::new(gtm(1, &g_ctx(4)))),
            &gt,
        );
        let w4 = Type::W {
            shape_level: lvar(1),
            pos_level: lvar(0),
            shape: Rc::new(gty(3, &g_ctx(4))),
            pos: Rc::new(gty(2, &gx)),
        };
        let u_t_at_ua = Type::GlobalTy {
            var: GlobalVar(2),
            subst: LocalSubst::id(&g_ctx(4)).extended(Rc::new(gtm(1, &g_ctx(4)))),
        };
        let f_ty = Type::Pi {
            dom_level: lvar(0),
            cod_level: lmax.clone(),
            dom: Rc::new(u_t_at_ua),
            cod: Rc::new(w4.shift_local(1)),
        };
        let x_f = inst_tm_motive(
            m_tm,
            (2, 5, 3),
            Level::max(lvar(0), lmax.clone()),
            g_ctx(4),
            f_ty,
            Term::BoxTm(Rc::new(gtm(0, &g_ctx(4)))),
            &gt,
        );
        let code = Term::Sup {
            shape_level: lvar(1),
            pos_level: lvar(0),
            shape_ty: Rc::new(gty(3, &g_ctx(4))),
            pos_ty: Rc::new(gty(2, &gx)),
            label: Rc::new(gtm(1, &g_ctx(4))),
            children: Rc::new(gtm(0, &g_ctx(4))),
        };
        // u_f's binding type, scoped over [g, U_S, U_T, u_a] (g=3, U_S=2,
        // U_T=1, u_a=0).
        let gx3 = ext_ctx(&g_ctx(3), gty(2, &g_ctx(3)), lvar(1));
        let w3 = Type::W {
            shape_level: lvar(1),
            pos_level: lvar(0),
            shape: Rc::new(gty(2, &g_ctx(3))),
            pos: Rc::new(gty(1, &gx3)),
        };
        let u_t_at_ua_bind = Type::GlobalTy {
            var: GlobalVar(1),
            subst: LocalSubst::id(&g_ctx(3)).extended(Rc::new(gtm(0, &g_ctx(3)))),
        };
        let f_ty_bind = Type::Pi {
            dom_level: lvar(0),
            cod_level: lmax.clone(),
            dom: Rc::new(u_t_at_ua_bind),
            cod: Rc::new(w3.shift_local(1)),
        };
        BranchSpec {
            tele: Tele {
                univs: 2,
                globals: vec![
                    GlobalBinding::Ctx,
                    GlobalBinding::Ty { ctx: g_ctx(0), layer: Layer::Code, level: lvar(1) },
                    GlobalBinding::Ty {
                        ctx: ext_ctx(&g_ctx(1), gty(0, &g_ctx(1)), lvar(1)),
                        layer: Layer::Code,
                        level: lvar(0),
                    },
                    GlobalBinding::Tm {
                        ctx: g_ctx(2),
                        layer: Layer::Code,
                        ty: Rc::new(gty(1, &g_ctx(2))),
                        level: lvar(1),
                    },
                    GlobalBinding::Tm {
                        ctx: g_ctx(3),
                        layer: Layer::Code,
                        ty: Rc::new(f_ty_bind),
                        level: Level::max(lvar(0), lmax.clone()),
                    },
                ],
                locals: vec![
                    (Rc::new(x_s), l1.shift(2, 0)),
                    (Rc::new(x_t), l1.shift(2, 0)),
                    (Rc::new(x_a), l2.shift(2, 0)),
                    (Rc::new(x_f), l2.shift(2, 0)),
                ],
            },
            ty: Rc::new(inst_tm_motive(
                m_tm,
                (2, 5, 4),
                lmax,
                g_ctx(4),
                w4,
                Term::BoxTm(Rc::new(code)),
                &gt,
            )),
            level: l2.shift(2, 0),
        }
    };

    // (ℓ, ℓ', ℓ'', g, U_S : Typ_c(g, ℓ), U_T : Typ_c((g, x : U_S^id @ ℓ), ℓ'),
    //  U_M : Typ_c((g, z : W(x:U_S^id).U_T^id @ ℓ⊔ℓ'), ℓ''),
    //  u_s : Trm_c((g, a : U_S^id @ ℓ, f : Π(y:U_T^{id,a/x}). W @ ℓ⊔ℓ',
    //               ih : Π(y:U_T^{id,a/x}). U_M^{id, f y/z} @ ℓ'⊔ℓ'')
    //        ⊢ U_M^{id, sup(a,f)/z} @ ℓ''),
    //  u_t : Trm_c(g ⊢ W(x:U_S^id).U_T^id @ ℓ⊔ℓ'),
    //  x_S, x_T, x_M, x_s, x_t. t_elimW)
    //   : M_Trm[ℓ''/ℓ, g/g, U_M^{id, u_t^id/z}/U_T,
    //           box (elim_W (x:U_S^id.U_T^id) (z. U_M^id) (a f ih. u_s^id)
    //                u_t^id)/x_t]
    // A positive dependent eliminator; x_M at the *type* motive. Extension.
    let tm_elim_w = {
        let gt = gt(3, 6);
        // telescope view: g = 5, U_S = 4, U_T = 3, U_M = 2, u_s = 1, u_t = 0.
        // Univs: ℓ = lvar(2), ℓ' = lvar(1), ℓ'' = lvar(0).
        let lmax = Level::max(lvar(2), lvar(1));
        let gx = ext_ctx(&g_ctx(5), gty(4, &g_ctx(5)), lvar(2));
        let w5 = Type::W {
            shape_level: lvar(2),
            pos_level: lvar(1),
            shape: Rc::new(gty(4, &g_ctx(5))),
            pos: Rc::new(gty(3, &gx)),
        };
        let gz = ext_ctx(&g_ctx(5), w5.clone(), lmax.clone());
        // Step context (g, a : U_S, f : Π(y:U_T^{id,a/x}). W,
        // ih : Π(y:U_T^{id,a/x}). U_M^{id, f y/z}) — in (g, a), U_T^{id,a/x}
        // is gty(3, gx) itself (a sits where the binder x was), as in
        // typing.rs/reduce.rs.
        let f_ty = Type::Pi {
            dom_level: lvar(1),
            cod_level: lmax.clone(),
            dom: Rc::new(gty(3, &gx)),
            cod: Rc::new(w5.shift_local(2)),
        };
        let gaf = ext_ctx(&gx, f_ty, Level::max(lvar(1), lmax.clone()));
        let f_y = Term::App {
            fun: Rc::new(Term::Var(LocalVar(1))),
            dom_level: lvar(1),
            cod_level: lmax.clone(),
            dom: Rc::new(gty(3, &gx).shift_local(2)),
            cod: Rc::new(w5.shift_local(4)),
            arg: Rc::new(Term::Var(LocalVar(0))),
        };
        let u_m_at_fy = Type::GlobalTy {
            var: GlobalVar(2),
            subst: LocalSubst::id(&g_ctx(5)).shift_local(3).extended(Rc::new(f_y)),
        };
        let ih_ty = Type::Pi {
            dom_level: lvar(1),
            cod_level: lvar(0),
            dom: Rc::new(gty(3, &gx).shift_local(1)),
            cod: Rc::new(u_m_at_fy),
        };
        let gafi = ext_ctx(&gaf, ih_ty, Level::max(lvar(1), lvar(0)));
        let Type::W { shape: s2, pos: p2, .. } = w5.shift_local(2) else {
            unreachable!()
        };
        let sup_af = Term::Sup {
            shape_level: lvar(2),
            pos_level: lvar(1),
            shape_ty: s2,
            pos_ty: p2,
            label: Rc::new(Term::Var(LocalVar(1))),
            children: Rc::new(Term::Var(LocalVar(0))),
        };
        let u_m_at_sup = Type::GlobalTy {
            var: GlobalVar(2),
            subst: LocalSubst::id(&g_ctx(5))
                .shift_local(3)
                .extended(Rc::new(sup_af.shift_local(1))),
        };
        let x_s = inst_ty_motive(
            m_ty,
            (3, 6, 0),
            lvar(2),
            g_ctx(5),
            Term::BoxTy(Rc::new(gty(4, &g_ctx(5)))),
            &gt,
        );
        let x_t = inst_ty_motive(
            m_ty,
            (3, 6, 1),
            lvar(1),
            gx.clone(),
            Term::BoxTy(Rc::new(gty(3, &gx))),
            &gt,
        );
        let x_m = inst_ty_motive(
            m_ty,
            (3, 6, 2),
            lvar(0),
            gz.clone(),
            Term::BoxTy(Rc::new(gty(2, &gz))),
            &gt,
        );
        let x_step = inst_tm_motive(
            m_tm,
            (3, 6, 3),
            lvar(0),
            gafi.clone(),
            u_m_at_sup.clone(),
            Term::BoxTm(Rc::new(gtm(1, &gafi))),
            &gt,
        );
        let x_scrut = inst_tm_motive(
            m_tm,
            (3, 6, 4),
            lmax.clone(),
            g_ctx(5),
            w5.clone(),
            Term::BoxTm(Rc::new(gtm(0, &g_ctx(5)))),
            &gt,
        );
        let code = Term::ElimW {
            shape_level: lvar(2),
            pos_level: lvar(1),
            motive_level: lvar(0),
            shape: Rc::new(gty(4, &g_ctx(5))),
            pos: Rc::new(gty(3, &gx)),
            motive: Rc::new(gty(2, &gz)),
            step: Rc::new(gtm(1, &gafi)),
            scrut: Rc::new(gtm(0, &g_ctx(5))),
        };
        let u_m_at_scrut = Type::GlobalTy {
            var: GlobalVar(2),
            subst: LocalSubst::id(&g_ctx(5)).extended(Rc::new(gtm(0, &g_ctx(5)))),
        };
        // -- global bindings, each scoped in its own Ψ-prefix --
        // U_M's context (g, z : W), prefix (g, U_S, U_T): g=2, U_S=1, U_T=0.
        let gx2 = ext_ctx(&g_ctx(2), gty(1, &g_ctx(2)), lvar(2));
        let w2 = Type::W {
            shape_level: lvar(2),
            pos_level: lvar(1),
            shape: Rc::new(gty(1, &g_ctx(2))),
            pos: Rc::new(gty(0, &gx2)),
        };
        // u_s's binding, prefix (g, U_S, U_T, U_M): g=3, U_S=2, U_T=1, U_M=0.
        let gx3 = ext_ctx(&g_ctx(3), gty(2, &g_ctx(3)), lvar(2));
        let w3 = Type::W {
            shape_level: lvar(2),
            pos_level: lvar(1),
            shape: Rc::new(gty(2, &g_ctx(3))),
            pos: Rc::new(gty(1, &gx3)),
        };
        let f_ty3 = Type::Pi {
            dom_level: lvar(1),
            cod_level: lmax.clone(),
            dom: Rc::new(gty(1, &gx3)),
            cod: Rc::new(w3.shift_local(2)),
        };
        let gaf3 = ext_ctx(&gx3, f_ty3, Level::max(lvar(1), lmax.clone()));
        let f_y3 = Term::App {
            fun: Rc::new(Term::Var(LocalVar(1))),
            dom_level: lvar(1),
            cod_level: lmax.clone(),
            dom: Rc::new(gty(1, &gx3).shift_local(2)),
            cod: Rc::new(w3.shift_local(4)),
            arg: Rc::new(Term::Var(LocalVar(0))),
        };
        let u_m_at_fy3 = Type::GlobalTy {
            var: GlobalVar(0),
            subst: LocalSubst::id(&g_ctx(3)).shift_local(3).extended(Rc::new(f_y3)),
        };
        let ih_ty3 = Type::Pi {
            dom_level: lvar(1),
            cod_level: lvar(0),
            dom: Rc::new(gty(1, &gx3).shift_local(1)),
            cod: Rc::new(u_m_at_fy3),
        };
        let gafi3 = ext_ctx(&gaf3, ih_ty3, Level::max(lvar(1), lvar(0)));
        let Type::W { shape: s23, pos: p23, .. } = w3.shift_local(2) else {
            unreachable!()
        };
        let sup3 = Term::Sup {
            shape_level: lvar(2),
            pos_level: lvar(1),
            shape_ty: s23,
            pos_ty: p23,
            label: Rc::new(Term::Var(LocalVar(1))),
            children: Rc::new(Term::Var(LocalVar(0))),
        };
        let u_m_bind_s = Type::GlobalTy {
            var: GlobalVar(0),
            subst: LocalSubst::id(&g_ctx(3))
                .shift_local(3)
                .extended(Rc::new(sup3.shift_local(1))),
        };
        // u_t's binding, prefix (g, U_S, U_T, U_M, u_s): g=4, U_S=3, U_T=2.
        let gx4 = ext_ctx(&g_ctx(4), gty(3, &g_ctx(4)), lvar(2));
        let w4 = Type::W {
            shape_level: lvar(2),
            pos_level: lvar(1),
            shape: Rc::new(gty(3, &g_ctx(4))),
            pos: Rc::new(gty(2, &gx4)),
        };
        BranchSpec {
            tele: Tele {
                univs: 3,
                globals: vec![
                    GlobalBinding::Ctx,
                    GlobalBinding::Ty { ctx: g_ctx(0), layer: Layer::Code, level: lvar(2) },
                    GlobalBinding::Ty {
                        ctx: ext_ctx(&g_ctx(1), gty(0, &g_ctx(1)), lvar(2)),
                        layer: Layer::Code,
                        level: lvar(1),
                    },
                    GlobalBinding::Ty {
                        ctx: ext_ctx(&g_ctx(2), w2, lmax.clone()),
                        layer: Layer::Code,
                        level: lvar(0),
                    },
                    GlobalBinding::Tm {
                        ctx: gafi3,
                        layer: Layer::Code,
                        ty: Rc::new(u_m_bind_s),
                        level: lvar(0),
                    },
                    GlobalBinding::Tm {
                        ctx: g_ctx(4),
                        layer: Layer::Code,
                        ty: Rc::new(w4),
                        level: lmax.clone(),
                    },
                ],
                locals: vec![
                    (Rc::new(x_s), l1.shift(3, 0)),
                    (Rc::new(x_t), l1.shift(3, 0)),
                    (Rc::new(x_m), l1.shift(3, 0)),
                    (Rc::new(x_step), l2.shift(3, 0)),
                    (Rc::new(x_scrut), l2.shift(3, 0)),
                ],
            },
            ty: Rc::new(inst_tm_motive(
                m_tm,
                (3, 6, 5),
                lvar(0),
                g_ctx(5),
                u_m_at_scrut,
                Term::BoxTm(Rc::new(code)),
                &gt,
            )),
            level: l2.shift(3, 0),
        }
    };

    [
        ty_nat, ty_pi, ty_ty, ty_el, ty_id, ty_sigma, ty_unit, ty_empty, tm_var, tm_nat,
        tm_pi, tm_ty, tm_zero, tm_succ, tm_elim_nat, tm_lam, tm_app, tm_id, tm_refl, tm_j,
        tm_sigma, tm_pair, tm_fst, tm_snd, tm_unit, tm_empty, tm_triv, tm_elim_empty, ty_sum,
        tm_sum, tm_inl, tm_inr, tm_case, ty_w, tm_w, tm_sup, tm_elim_w,
    ]
}
