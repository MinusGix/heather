//! The code-recursor telescopes of ch. 04 (§More Typing and Equivalence
//! Judgments): the two motive scopes `G_M` and the 13 branch telescopes
//! `G_Typ G_Trm`, each with its expected (motive-instantiated) type.
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

/// The 13 branches, in [`branch_specs`] order (= `Branches` field order).
pub(crate) fn branch_terms(b: &Branches) -> [&Rc<Term>; 13] {
    [
        &b.ty_nat,
        &b.ty_pi,
        &b.ty_ty,
        &b.ty_el,
        &b.tm_var,
        &b.tm_nat,
        &b.tm_pi,
        &b.tm_ty,
        &b.tm_zero,
        &b.tm_succ,
        &b.tm_elim_nat,
        &b.tm_lam,
        &b.tm_app,
    ]
}

/// The 13 branch telescopes `G_Typ G_Trm` with their expected types, built
/// from the given motives (for conversion: the *left* side's, matching its
/// left-biased inference). `gamma` is the ambient local context (before any
/// telescope), used only for the shape of the identity substitutions in the
/// motive instantiations.
pub(crate) fn branch_specs(
    motives: &Motives,
    l1: &Level,
    l2: &Level,
    gamma: &LocalCtx,
) -> [BranchSpec; 13] {
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

    [
        ty_nat, ty_pi, ty_ty, ty_el, tm_var, tm_nat, tm_pi, tm_ty, tm_zero, tm_succ,
        tm_elim_nat, tm_lam, tm_app,
    ]
}
