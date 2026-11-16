//! The code-recursor telescopes of ch. 04 (§More Typing and Equivalence
//! Judgments): the two motive scopes `G_M` and the 65 branch telescopes
//! `G_Typ G_Trm` (13 from ch. 04, the rest the extension formers' —
//! `docs/kernel/delam-extensions.md`), each with its expected
//! (motive-instantiated) type.
//!
//! This is the single most error-prone part of the theory, so the tables
//! live here **once** and are consumed by both the convertibility checker
//! ([`crate::conv`], comparing branches pairwise at these types) and the
//! type checker ([`crate::typing`], checking branches against these types).
//! They must also stay in sync with `subst.rs`'s `map_branches` depths and
//! `reduce.rs`'s β-instantiations, which nothing checks but the
//! identity-recursor typing test end to end
//! (`issues/kernel-binder-count-tables.md`).
//!
//! Scoping convention for a telescope `(ℓ⃗; B⃗; x⃗)`: `univs` universe binders
//! are pushed first, then the global bindings (each scoped over `L, ℓ⃗` and
//! its Ψ-prefix), then the recursive-call local entries (each scoped over
//! the whole telescope plus the previous locals, with the ambient Γ already
//! weakened into the telescope).

use crate::rc::Rc;

use crate::layer::Layer;
use crate::level::{Level, UnivVar};
use crate::subst::{GlobalEntry, GlobalSubst};
use crate::term::{
    inst_motive2, iwf_children_ty, iwf_motive_scrut_ty, iwf_step_telescope, m_out_ty, m_step_ty,
    wf_step_telescope, Branches, CtxEntry, GlobalBinding, GlobalCtx, GlobalVar, IWfSig, LocalCtx,
    LocalSubst, LocalVar, Motives, SealedProof, Term, Type,
};

// ---------------------------------------------------------------------------
// Small constructors
// ---------------------------------------------------------------------------

pub(crate) fn lvar(i: u32) -> Level {
    Level::Var(UnivVar(i))
}

/// The context `g` for the context variable at de Bruijn index `i`.
pub(crate) fn g_ctx(i: u32) -> LocalCtx {
    LocalCtx::ctx_var(GlobalVar::index(i))
}

/// `Δ, x : T @ l`.
pub(crate) fn ext_ctx(base: &LocalCtx, ty: Type, level: Level) -> LocalCtx {
    let mut c = base.clone();
    c.entries.push(CtxEntry { ty: Rc::new(ty), level });
    c
}

/// `U^{id_Δ}` for the global type variable `var` with index context `ctx`.
pub(crate) fn gty(var: u32, ctx: &LocalCtx) -> Type {
    Type::GlobalTy { var: GlobalVar::index(var), subst: LocalSubst::id(ctx) }
}

/// `u^{id_Δ}` for the global term variable `var` with index context `ctx`.
pub(crate) fn gtm(var: u32, ctx: &LocalCtx) -> Term {
    Term::GlobalTm { var: GlobalVar::index(var), subst: LocalSubst::id(ctx) }
}

/// Weaken every binding of Ψ by `by` universe variables (all bindings are
/// scoped in the same L).
pub(crate) fn shift_univ_psi(psi: &GlobalCtx, by: u32) -> GlobalCtx {
    if by == 0 {
        return psi.clone();
    }
    let mut out = GlobalCtx::new(
        psi.bindings
            .iter()
            .map(|b| match b {
                GlobalBinding::Ctx => GlobalBinding::Ctx,
                GlobalBinding::Ty { ctx, layer, level } => GlobalBinding::Ty {
                    ctx: ctx.shift_univ(by),
                    layer: *layer,
                    level: level.shift(by, 0),
                },
                GlobalBinding::Tm { ctx, layer, ty, level, body } => GlobalBinding::Tm {
                    ctx: ctx.shift_univ(by),
                    layer: *layer,
                    ty: Rc::new(ty.shift_univ(by)),
                    level: level.shift(by, 0),
                    // A definition's body lives in the same universe scope
                    // as its type, so it shifts with it.
                    body: body.as_ref().map(|t| Rc::new(t.shift_univ(by))),
                },
            })
            .collect(),
    )
    // The same bindings, so the same signature: a position names what it
    // named.
    .with_consts(psi.consts());
    // A sealed proof shifts with its binding, as a body does — when it is
    // first needed, so a telescope does not load every lazily kept proof.
    for (i, t) in psi.sealed.iter() {
        out.seal_kept(i, Rc::new(SealedProof::derived(Rc::clone(t), move |t| t.shift_univ(by))));
    }
    out.withheld = psi.withheld.clone();
    out
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

/// The 65 branch names, in [`branch_specs`] order — for diagnostics that
/// must name a branch without printing a term, and for the surface
/// `match code`, whose arms are **keyed to these names**: the table below is
/// the single source of truth for what branches exist and in what order, and
/// the elaborator reads it rather than restating it.
pub const BRANCH_NAMES: [&str; 65] = [
    "ty_nat",
    "ty_pi",
    "ty_ty",
    "ty_el",
    "ty_id",
    "ty_sigma",
    "ty_unit",
    "ty_empty",
    "tm_var",
    "tm_nat",
    "tm_pi",
    "tm_ty",
    "tm_zero",
    "tm_succ",
    "tm_elim_nat",
    "tm_lam",
    "tm_app",
    "tm_id",
    "tm_refl",
    "tm_j",
    "tm_sigma",
    "tm_pair",
    "tm_fst",
    "tm_snd",
    "tm_unit",
    "tm_empty",
    "tm_triv",
    "tm_elim_empty",
    "ty_sum",
    "tm_sum",
    "tm_inl",
    "tm_inr",
    "tm_case",
    "ty_w",
    "tm_w",
    "tm_sup",
    "tm_elim_w",
    "ty_vec",
    "tm_vec",
    "ty_fin",
    "tm_fin",
    "ty_wf",
    "tm_wf",
    "tm_supf",
    "tm_elim_wf",
    "ty_seq",
    "tm_seq",
    "ty_sempty",
    "tm_sempty",
    "tm_srefl",
    "tm_elim_sempty",
    "ty_squash",
    "tm_squash",
    "tm_squash_in",
    "tm_elim_squash",
    "ty_m",
    "tm_m",
    "tm_corec",
    "tm_out",
    "ty_dvec",
    "tm_dvec",
    "ty_iwf",
    "tm_iwf",
    "tm_sup_i",
    "tm_elim_iwf",
];

/// The 65 branches, in [`branch_specs`] order (= `Branches` field order).
pub(crate) fn branch_terms(b: &Branches) -> [&Rc<Term>; 65] {
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
        &b.ty_vec,
        &b.tm_vec,
        &b.ty_fin,
        &b.tm_fin,
        &b.ty_wf,
        &b.tm_wf,
        &b.tm_supf,
        &b.tm_elim_wf,
        &b.ty_seq,
        &b.tm_seq,
        &b.ty_sempty,
        &b.tm_sempty,
        &b.tm_srefl,
        &b.tm_elim_sempty,
        &b.ty_squash,
        &b.tm_squash,
        &b.tm_squash_in,
        &b.tm_elim_squash,
        &b.ty_m,
        &b.tm_m,
        &b.tm_corec,
        &b.tm_out,
        &b.ty_dvec,
        &b.tm_dvec,
        &b.ty_iwf,
        &b.tm_iwf,
        &b.tm_sup_i,
        &b.tm_elim_iwf,
    ]
}

/// What a caller outside the kernel needs in order to *write* a branch: how
/// many binders the branch telescope pushes, and the types of its
/// recursive-call locals under it. Everything else about a telescope (which
/// globals, at which contexts) is the kernel's business, because a branch term
/// that mentions them cannot be written at the surface anyway
/// (docs/archive/certgen-transcriber-in-language-design.md §3).
pub struct BranchShape {
    pub name: &'static str,
    /// Universe binders the telescope pushes, innermost-last.
    pub univs: u32,
    /// Global binders (`g`, the `U_…`/`u_…` sub-code) the telescope pushes,
    /// innermost-last and prefix-scoped, exactly as Ψ holds them. A client
    /// that elaborates a branch body has to put these in scope even though
    /// nothing can name them: the *indices* of the ambient globals move by
    /// their count.
    pub globals: Vec<GlobalBinding>,
    /// The recursive-call locals, `(type, level)`, innermost-last — the only
    /// telescope entries a surface arm may name.
    pub locals: Vec<(Rc<Type>, Level)>,
    /// The branch's expected type under its own telescope.
    pub ty: Rc<Type>,
    pub level: Level,
}

/// The 65 branch shapes at the given motives, in [`BRANCH_NAMES`] order.
///
/// Derived from [`branch_specs`], never restated: a client that binds arm
/// variables by position stays correct when a branch's telescope changes,
/// and gets a compile-time-checked count for free.
pub fn branch_shapes(
    motives: &Motives,
    l1: &Level,
    l2: &Level,
    gamma: &LocalCtx,
) -> Vec<BranchShape> {
    branch_specs(motives, l1, l2, gamma)
        .into_iter()
        .zip(BRANCH_NAMES)
        .map(|(spec, name)| BranchShape {
            name,
            univs: spec.tele.univs,
            globals: spec.tele.globals,
            locals: spec.tele.locals,
            ty: spec.ty,
            level: spec.level,
        })
        .collect()
}

/// [`Branches`] from 65 terms in [`BRANCH_NAMES`] order — the inverse of
/// [`branch_terms`], for clients that build the table by index.
pub fn branches_from(t: [Rc<Term>; 65]) -> Branches {
    let [
        ty_nat, ty_pi, ty_ty, ty_el, ty_id, ty_sigma, ty_unit, ty_empty, tm_var, tm_nat,
        tm_pi, tm_ty, tm_zero, tm_succ, tm_elim_nat, tm_lam, tm_app, tm_id, tm_refl, tm_j,
        tm_sigma, tm_pair, tm_fst, tm_snd, tm_unit, tm_empty, tm_triv, tm_elim_empty, ty_sum,
        tm_sum, tm_inl, tm_inr, tm_case, ty_w, tm_w, tm_sup, tm_elim_w, ty_vec, tm_vec,
        ty_fin, tm_fin, ty_wf, tm_wf, tm_supf, tm_elim_wf, ty_seq, tm_seq, ty_sempty,
        tm_sempty, tm_srefl, tm_elim_sempty,
        ty_squash, tm_squash, tm_squash_in, tm_elim_squash,
        ty_m, tm_m, tm_corec, tm_out,
        ty_dvec, tm_dvec, ty_iwf, tm_iwf, tm_sup_i, tm_elim_iwf,
    ] = t;
    Branches {
        ty_nat, ty_pi, ty_ty, ty_el, ty_id, ty_sigma, ty_unit, ty_empty, tm_var, tm_nat,
        tm_pi, tm_ty, tm_zero, tm_succ, tm_elim_nat, tm_lam, tm_app, tm_id, tm_refl, tm_j,
        tm_sigma, tm_pair, tm_fst, tm_snd, tm_unit, tm_empty, tm_triv, tm_elim_empty, ty_sum,
        tm_sum, tm_inl, tm_inr, tm_case, ty_w, tm_w, tm_sup, tm_elim_w, ty_vec, tm_vec,
        ty_fin, tm_fin, ty_wf, tm_wf, tm_supf, tm_elim_wf, ty_seq, tm_seq, ty_sempty,
        tm_sempty, tm_srefl, tm_elim_sempty,
        ty_squash, tm_squash, tm_squash_in, tm_elim_squash,
        ty_m, tm_m, tm_corec, tm_out,
        ty_dvec, tm_dvec, ty_iwf, tm_iwf, tm_sup_i, tm_elim_iwf,
    }
}

/// One piece of an `M` signature as a branch telescope binds it: the type
/// global `U^{id}` (`ty_m`, `tm_corec`, `tm_out`), or `El` of the code global
/// `u^{id}` (`tm_m`) — docs/kernel/kernel-m-codes-design.md §2.
fn m_piece(coded: bool, var: u32, ctx: &LocalCtx, level: &Level) -> Type {
    if coded {
        Type::El { level: level.clone(), tm: Rc::new(gtm(var, ctx)) }
    } else {
        gty(var, ctx)
    }
}

/// The signature `(I; i. S; i s. P; i s p. o)` over globals `g, I, S, P, o`
/// with `o` at index `k` (so `k` globals follow it), and the three contexts
/// its binders open: `(g, i)`, `(g, i, s)`, `(g, i, s, p)`.
struct MView {
    sig: Rc<crate::term::MSig>,
    g: LocalCtx,
    gi: LocalCtx,
    gis: LocalCtx,
    gisp: LocalCtx,
}

fn m_view(coded: bool, k: u32, l: &Level, lp: &Level, li: &Level) -> MView {
    let g = g_ctx(k + 4);
    let idx = m_piece(coded, k + 3, &g, li);
    let gi = ext_ctx(&g, idx.clone(), li.clone());
    let shape = m_piece(coded, k + 2, &gi, l);
    let gis = ext_ctx(&gi, shape.clone(), l.clone());
    let pos = m_piece(coded, k + 1, &gis, lp);
    let gisp = ext_ctx(&gis, pos.clone(), lp.clone());
    let next = gtm(k, &gisp);
    MView {
        sig: Rc::new(crate::term::MSig {
            level: l.clone(),
            pos_level: lp.clone(),
            idx_level: li.clone(),
            idx: Rc::new(idx),
            shape: Rc::new(shape),
            pos: Rc::new(pos),
            next: Rc::new(next),
        }),
        g,
        gi,
        gis,
        gisp,
    }
}

/// The five globals `g, I, S, P, o` every `M` branch opens with, each scoped
/// in its own Ψ-prefix: types (`Typ_c`) or, `coded`, terms of `Ty` (`Trm_c`).
fn m_sig_globals(coded: bool, l: &Level, lp: &Level, li: &Level) -> Vec<GlobalBinding> {
    let code_or_ty = |ctx: LocalCtx, level: &Level| {
        if coded {
            GlobalBinding::Tm {
                ctx,
                layer: Layer::Code,
                ty: Rc::new(Type::Ty(level.clone())),
                level: Level::succ(level.clone()),
                body: None,
            }
        } else {
            GlobalBinding::Ty { ctx, layer: Layer::Code, level: level.clone() }
        }
    };
    // Prefix (g): g = 0.
    let i_ctx = g_ctx(0);
    // Prefix (g, I): g = 1, I = 0.
    let g1 = g_ctx(1);
    let s_ctx = ext_ctx(&g1, m_piece(coded, 0, &g1, li), li.clone());
    // Prefix (g, I, S): g = 2, I = 1, S = 0.
    let g2 = g_ctx(2);
    let gi2 = ext_ctx(&g2, m_piece(coded, 1, &g2, li), li.clone());
    let p_ctx = ext_ctx(&gi2, m_piece(coded, 0, &gi2, l), l.clone());
    // Prefix (g, I, S, P): g = 3, I = 2, S = 1, P = 0.
    let g3 = g_ctx(3);
    let idx3 = m_piece(coded, 2, &g3, li);
    let gi3 = ext_ctx(&g3, idx3.clone(), li.clone());
    let gis3 = ext_ctx(&gi3, m_piece(coded, 1, &gi3, l), l.clone());
    let o_ctx = ext_ctx(&gis3, m_piece(coded, 0, &gis3, lp), lp.clone());
    vec![
        GlobalBinding::Ctx,
        code_or_ty(i_ctx, li),
        code_or_ty(s_ctx, l),
        code_or_ty(p_ctx, lp),
        GlobalBinding::Tm {
            ctx: o_ctx,
            layer: Layer::Code,
            ty: Rc::new(idx3.shift_local(3)),
            level: li.clone(),
            body: None,
        },
    ]
}

/// The `IWf` signature `(I; x:S. n; x. o; x i. c)` over globals
/// `g, I, S, n, o, c` with `c` at index `k` (so `k` globals follow it), and
/// the two contexts its binders open: `(g, x : S)` and `(g, x, i : Fin n)`
/// (docs/kernel/iwf-former-design.md §6). `coded`, the index type and the shapes are
/// `El` of code globals, as [`m_view`]'s pieces are.
struct IWfView {
    sig: Rc<IWfSig>,
    g: LocalCtx,
    gx: LocalCtx,
    gxi: LocalCtx,
}

fn iwf_view(coded: bool, k: u32, l: &Level, li: &Level) -> IWfView {
    let g = g_ctx(k + 5);
    let idx = m_piece(coded, k + 4, &g, li);
    let shape = m_piece(coded, k + 3, &g, l);
    let gx = ext_ctx(&g, shape.clone(), l.clone());
    let arity = gtm(k + 2, &gx);
    let gxi = ext_ctx(&gx, Type::Fin { len: Rc::new(arity.clone()) }, Level::Zero);
    IWfView {
        sig: Rc::new(IWfSig {
            level: l.clone(),
            idx_level: li.clone(),
            idx: Rc::new(idx),
            shape: Rc::new(shape),
            arity: Rc::new(arity),
            out: Rc::new(gtm(k + 1, &gx)),
            child: Rc::new(gtm(k, &gxi)),
        }),
        g,
        gx,
        gxi,
    }
}

/// The six globals `g, I, S, n, o, c` every `IWf` branch opens with, each
/// scoped in its own Ψ-prefix: the index type and the shapes as types
/// (`Typ_c`) or, `coded`, as terms of `Ty` (`Trm_c`). heather-coq's
/// `brDecls 57`'s first six, innermost-last.
fn iwf_sig_globals(coded: bool, l: &Level, li: &Level) -> Vec<GlobalBinding> {
    let code_or_ty = |ctx: LocalCtx, level: &Level| {
        if coded {
            GlobalBinding::Tm {
                ctx,
                layer: Layer::Code,
                ty: Rc::new(Type::Ty(level.clone())),
                level: Level::succ(level.clone()),
                body: None,
            }
        } else {
            GlobalBinding::Ty { ctx, layer: Layer::Code, level: level.clone() }
        }
    };
    // Prefix (g, I, S): g = 2, I = 1, S = 0.
    let g2 = g_ctx(2);
    let n_ctx = ext_ctx(&g2, m_piece(coded, 0, &g2, l), l.clone());
    // Prefix (g, I, S, n): g = 3, I = 2, S = 1, n = 0.
    let g3 = g_ctx(3);
    let o_ctx = ext_ctx(&g3, m_piece(coded, 1, &g3, l), l.clone());
    let o_ty = m_piece(coded, 2, &g3, li).shift_local(1);
    // Prefix (g, I, S, n, o): g = 4, I = 3, S = 2, n = 1, o = 0.
    let g4 = g_ctx(4);
    let gx4 = ext_ctx(&g4, m_piece(coded, 2, &g4, l), l.clone());
    let c_ctx = ext_ctx(&gx4, Type::Fin { len: Rc::new(gtm(1, &gx4)) }, Level::Zero);
    let c_ty = m_piece(coded, 3, &g4, li).shift_local(2);
    vec![
        GlobalBinding::Ctx,
        code_or_ty(g_ctx(0), li),
        code_or_ty(g_ctx(1), l),
        GlobalBinding::Tm {
            ctx: n_ctx,
            layer: Layer::Code,
            ty: Rc::new(Type::Nat),
            level: Level::Zero,
            body: None,
        },
        GlobalBinding::Tm { ctx: o_ctx, layer: Layer::Code, ty: Rc::new(o_ty), level: li.clone(), body: None },
        GlobalBinding::Tm { ctx: c_ctx, layer: Layer::Code, ty: Rc::new(c_ty), level: li.clone(), body: None },
    ]
}

/// The 65 branch telescopes `G_Typ G_Trm` with their expected types, built
/// from the given motives (for conversion: the *left* side's, matching its
/// left-biased inference). `gamma` is the ambient local context (before any
/// telescope), used only for the shape of the identity substitutions in the
/// motive instantiations. The 13 ch. 04 branches come first in each group;
/// the rest are the extension formers' (`docs/kernel/delam-extensions.md`).
pub(crate) fn branch_specs(
    motives: &Motives,
    l1: &Level,
    l2: &Level,
    gamma: &LocalCtx,
) -> [BranchSpec; 65] {
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
                        body: None,
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
                        body: None,
                    },
                    GlobalBinding::Tm {
                        ctx: g_ctx(2),
                        layer: Layer::Code,
                        ty: Rc::new(gty(1, &g_ctx(2))),
                        level: lvar(0),
                        body: None,
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

    // (ℓ, g. t_Unit) : M_Typ[ℓ/ℓ, g/g, box (Unit^ℓ)/x_T]
    //   (extension; mirrors ty_nat plus Unit's level binder)
    let ty_unit = {
        let gt = gt(1, 1);
        BranchSpec {
            tele: Tele { univs: 1, globals: vec![GlobalBinding::Ctx], locals: vec![] },
            ty: Rc::new(inst_ty_motive(
                m_ty,
                (1, 1, 0),
                lvar(0),
                g_ctx(0),
                Term::BoxTy(Rc::new(Type::Unit { level: lvar(0) })),
                &gt,
            )),
            level: l1.shift(1, 0),
        }
    };

    // (ℓ, g. t_Empty) : M_Typ[ℓ/ℓ, g/g, box (Empty^ℓ)/x_T]
    //   (extension; mirrors ty_unit)
    let ty_empty = {
        let gt = gt(1, 1);
        BranchSpec {
            tele: Tele { univs: 1, globals: vec![GlobalBinding::Ctx], locals: vec![] },
            ty: Rc::new(inst_ty_motive(
                m_ty,
                (1, 1, 0),
                lvar(0),
                g_ctx(0),
                Term::BoxTy(Rc::new(Type::Empty { level: lvar(0) })),
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
                        body: None,
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
                        body: None,
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
                        body: None,
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
                        body: None,
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
        let motive_code = Type::GlobalTy { var: GlobalVar::index(3), subst: LocalSubst::id(&gx) };
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
            var: GlobalVar::index(3),
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
            var: GlobalVar::index(3),
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
        // The scrutinee's recursive call sits at the level of the scrutinee's
        // *type* — `Nat @ 0` — not at the motive's ℓ. Ch. 04 writes `ℓ/ℓ`
        // here, which contradicts its own `t_ze`/`t_succ` (both `0/ℓ` for the
        // same `Nat/U_T` slot) and the β rule; see
        // docs/kernel/delam-extensions.md §16.1 ([[recursor-elim-call-level-mismatch]]).
        let x_t = inst_tm_motive(
            m_tm,
            (1, 5, 3),
            Level::Zero,
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
            var: GlobalVar::index(3),
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
                            var: GlobalVar::index(0),
                            subst: LocalSubst::id(&g_ctx(1)).extended(Rc::new(Term::Zero)),
                        }),
                        level: lvar(0),
                        body: None,
                    },
                    GlobalBinding::Tm {
                        ctx: {
                            let gx = ext_ctx(&g_ctx(2), Type::Nat, Level::Zero);
                            let y_ty = Type::GlobalTy {
                                var: GlobalVar::index(1),
                                subst: LocalSubst::id(&gx),
                            };
                            ext_ctx(&gx, y_ty, lvar(0))
                        },
                        layer: Layer::Code,
                        ty: Rc::new(Type::GlobalTy {
                            var: GlobalVar::index(1),
                            subst: LocalSubst::id(&g_ctx(2))
                                .shift_local(2)
                                .extended(Rc::new(Term::Succ(Rc::new(Term::Var(
                                    LocalVar(1),
                                ))))),
                        }),
                        level: lvar(0),
                        body: None,
                    },
                    GlobalBinding::Tm {
                        ctx: g_ctx(3),
                        layer: Layer::Code,
                        ty: Rc::new(Type::Nat),
                        level: Level::Zero,
                        body: None,
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
                        body: None,
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
            var: GlobalVar::index(2),
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
                        body: None,
                    },
                    GlobalBinding::Tm {
                        ctx: g_ctx(3),
                        layer: Layer::Code,
                        ty: Rc::new(gty(2, &g_ctx(3))),
                        level: lvar(1),
                        body: None,
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
                        body: None,
                    },
                    GlobalBinding::Tm {
                        ctx: g_ctx(1),
                        layer: Layer::Code,
                        ty: Rc::new(Type::El {
                            level: lvar(0),
                            tm: Rc::new(gtm(0, &g_ctx(1))),
                        }),
                        level: lvar(0),
                        body: None,
                    },
                    GlobalBinding::Tm {
                        ctx: g_ctx(2),
                        layer: Layer::Code,
                        ty: Rc::new(Type::El {
                            level: lvar(0),
                            tm: Rc::new(gtm(1, &g_ctx(2))),
                        }),
                        level: lvar(0),
                        body: None,
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
                        body: None,
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
        let motive_code = Type::GlobalTy { var: GlobalVar::index(3), subst: LocalSubst::id(&gyp) };
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
            var: GlobalVar::index(3),
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
            var: GlobalVar::index(3),
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
                        body: None,
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
                            var: GlobalVar::index(0),
                            subst: LocalSubst::id(&g_ctx(3))
                                .extended(Rc::new(gtm(1, &g_ctx(3))))
                                .extended(Rc::new(Term::Refl {
                                    level: lvar(1),
                                    ty: Rc::new(gty(2, &g_ctx(3))),
                                    tm: Rc::new(gtm(1, &g_ctx(3))),
                                })),
                        }),
                        level: lvar(0),
                        body: None,
                    },
                    GlobalBinding::Tm {
                        ctx: g_ctx(4),
                        layer: Layer::Code,
                        ty: Rc::new(gty(3, &g_ctx(4))),
                        level: lvar(1),
                        body: None,
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
                        body: None,
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
                        body: None,
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
                        body: None,
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
            var: GlobalVar::index(2),
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
                        body: None,
                    },
                    GlobalBinding::Tm {
                        ctx: g_ctx(3),
                        layer: Layer::Code,
                        ty: Rc::new(Type::GlobalTy {
                            var: GlobalVar::index(1),
                            subst: LocalSubst::id(&g_ctx(3))
                                .extended(Rc::new(gtm(0, &g_ctx(3)))),
                        }),
                        level: lvar(0),
                        body: None,
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
                        body: None,
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
            var: GlobalVar::index(1),
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
                        body: None,
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

    // (ℓ, g. t'_Unit) : M_Trm[1+ℓ/ℓ, g/g, Ty ℓ/U_T, box (Unit^ℓ)/x_t]
    //   (extension; mirrors tm_nat — code of the encoding Unit^ℓ : Ty ℓ)
    let tm_unit = {
        let gt = gt(1, 1);
        BranchSpec {
            tele: Tele { univs: 1, globals: vec![GlobalBinding::Ctx], locals: vec![] },
            ty: Rc::new(inst_tm_motive(
                m_tm,
                (1, 1, 0),
                Level::succ(lvar(0)),
                g_ctx(0),
                Type::Ty(lvar(0)),
                Term::BoxTm(Rc::new(Term::TmUnit { level: lvar(0) })),
                &gt,
            )),
            level: l2.shift(1, 0),
        }
    };

    // (ℓ, g. t'_Empty) : M_Trm[1+ℓ/ℓ, g/g, Ty ℓ/U_T, box (Empty^ℓ)/x_t]
    //   (extension; mirrors tm_unit)
    let tm_empty = {
        let gt = gt(1, 1);
        BranchSpec {
            tele: Tele { univs: 1, globals: vec![GlobalBinding::Ctx], locals: vec![] },
            ty: Rc::new(inst_tm_motive(
                m_tm,
                (1, 1, 0),
                Level::succ(lvar(0)),
                g_ctx(0),
                Type::Ty(lvar(0)),
                Term::BoxTm(Rc::new(Term::TmEmpty { level: lvar(0) })),
                &gt,
            )),
            level: l2.shift(1, 0),
        }
    };

    // (ℓ, g. t_triv) : M_Trm[ℓ/ℓ, g/g, Unit^ℓ/U_T, box (⟨⟩^ℓ)/x_t]
    //   (extension; mirrors tm_zero — code of the intro ⟨⟩^ℓ : Unit^ℓ)
    let tm_triv = {
        let gt = gt(1, 1);
        BranchSpec {
            tele: Tele { univs: 1, globals: vec![GlobalBinding::Ctx], locals: vec![] },
            ty: Rc::new(inst_tm_motive(
                m_tm,
                (1, 1, 0),
                lvar(0),
                g_ctx(0),
                Type::Unit { level: lvar(0) },
                Term::BoxTm(Rc::new(Term::Triv { level: lvar(0) })),
                &gt,
            )),
            level: l2.shift(1, 0),
        }
    };

    // (ℓ, ℓ', g, U_M : Typ_c((g, x : Empty^ℓ' @ ℓ'), ℓ),
    //  u_t : Trm_c(g ⊢ Empty^ℓ' @ ℓ'), x_M, x_t. t_elimE)
    //   : M_Trm[ℓ/ℓ, g/g, U_M^{id, u_t^id/x}/U_T, box (elim_Empty …)/x_t]
    // Extension; mirrors tm_elim_nat minus the base/step branches.
    let tm_elim_empty = {
        let gt = gt(2, 3);
        // telescope view: ℓ = 1 (motive), ℓ' = 0 (scrutinee); g = 2, U_M = 1,
        // u_t = 0. `Empty` is level-indexed as of
        // docs/kernel/unit-empty-level-indexing.md, so the scrutinee's level is its
        // own binder rather than a hardcoded 0 — this is the one branch that
        // gains a *second* universe rather than a first.
        let empty = Type::Empty { level: lvar(0) };
        let gx = ext_ctx(&g_ctx(2), empty.clone(), lvar(0));
        let motive_code = Type::GlobalTy { var: GlobalVar::index(1), subst: LocalSubst::id(&gx) };
        let x_m = inst_ty_motive(
            m_ty,
            (2, 3, 0),
            lvar(1),
            gx.clone(),
            Term::BoxTy(Rc::new(motive_code.clone())),
            &gt,
        );
        // As in `tm_elim_nat`: the scrutinee's call is at the scrutinee's own
        // level ℓ' = lvar(0) (the level of `Empty^{ℓ'}`), not the motive's ℓ.
        // See docs/kernel/delam-extensions.md §7.7/§16.1.
        let x_t = inst_tm_motive(
            m_tm,
            (2, 3, 1),
            lvar(0),
            g_ctx(2),
            empty.clone(),
            Term::BoxTm(Rc::new(gtm(0, &g_ctx(2)))),
            &gt,
        );
        let code = Term::ElimEmpty {
            level: lvar(1),
            scrut_level: lvar(0),
            motive: Rc::new(motive_code),
            scrut: Rc::new(gtm(0, &g_ctx(2))),
        };
        let u_m_at_scrut = Type::GlobalTy {
            var: GlobalVar::index(1),
            subst: LocalSubst::id(&g_ctx(2)).extended(Rc::new(gtm(0, &g_ctx(2)))),
        };
        BranchSpec {
            tele: Tele {
                univs: 2,
                globals: vec![
                    GlobalBinding::Ctx,
                    GlobalBinding::Ty {
                        ctx: ext_ctx(&g_ctx(0), Type::Empty { level: lvar(0) }, lvar(0)),
                        layer: Layer::Code,
                        level: lvar(1),
                    },
                    GlobalBinding::Tm {
                        ctx: g_ctx(1),
                        layer: Layer::Code,
                        ty: Rc::new(Type::Empty { level: lvar(0) }),
                        level: lvar(0),
                        body: None,
                    },
                ],
                locals: vec![
                    (Rc::new(x_m), l1.shift(2, 0)),
                    (Rc::new(x_t), l2.shift(2, 0)),
                ],
            },
            ty: Rc::new(inst_tm_motive(
                m_tm,
                (2, 3, 2),
                lvar(1),
                g_ctx(2),
                u_m_at_scrut,
                Term::BoxTm(Rc::new(code)),
                &gt,
            )),
            level: l2.shift(2, 0),
        }
    };

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
                        body: None,
                    },
                    GlobalBinding::Tm {
                        ctx: g_ctx(1),
                        layer: Layer::Code,
                        ty: Rc::new(Type::Ty(lvar(0))),
                        level: Level::succ(lvar(0)),
                        body: None,
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
                        body: None,
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
                        body: None,
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
            var: GlobalVar::index(3),
            subst: LocalSubst::id(&g_ctx(6)).shift_local(1).extended(Rc::new(inl_x)),
        };
        let u_m_at_inr = Type::GlobalTy {
            var: GlobalVar::index(3),
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
            var: GlobalVar::index(3),
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
            var: GlobalVar::index(0),
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
            var: GlobalVar::index(1),
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
                        body: None,
                    },
                    GlobalBinding::Tm {
                        ctx: ext_ctx(&g_ctx(4), gty(2, &g_ctx(4)), lvar(1)),
                        layer: Layer::Code,
                        ty: Rc::new(u_m_bind_r),
                        level: lvar(0),
                        body: None,
                    },
                    GlobalBinding::Tm {
                        ctx: g_ctx(5),
                        layer: Layer::Code,
                        ty: Rc::new(sum_ut),
                        level: lmax.clone(),
                        body: None,
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
                        body: None,
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
                        body: None,
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
            var: GlobalVar::index(2),
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
            var: GlobalVar::index(1),
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
                        body: None,
                    },
                    GlobalBinding::Tm {
                        ctx: g_ctx(3),
                        layer: Layer::Code,
                        ty: Rc::new(f_ty_bind),
                        level: Level::max(lvar(0), lmax.clone()),
                        body: None,
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
            var: GlobalVar::index(2),
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
            var: GlobalVar::index(2),
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
            var: GlobalVar::index(2),
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
            var: GlobalVar::index(0),
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
            var: GlobalVar::index(0),
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
                        body: None,
                    },
                    GlobalBinding::Tm {
                        ctx: g_ctx(4),
                        layer: Layer::Code,
                        ty: Rc::new(w4),
                        level: lmax.clone(),
                        body: None,
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

    // -- finitary branching (docs/kernel/wf-former-design.md §6) --------------------

    // (ℓ, g, U_T : Typ_c(g, ℓ), u_k : Trm_c(g ⊢ Nat @ 0), x_T, x_k. t_Vec)
    //   : M_Typ[ℓ/ℓ, g/g, box Vec^ℓ(U_T^id; u_k^id)/x_T]
    // The length is a term in Δ (no binder), so x_k is at the *term* motive.
    let ty_vec = {
        let gt = gt(1, 3);
        // telescope view: g = 2, U_T = 1, u_k = 0
        let x_t = inst_ty_motive(
            m_ty,
            (1, 3, 0),
            lvar(0),
            g_ctx(2),
            Term::BoxTy(Rc::new(gty(1, &g_ctx(2)))),
            &gt,
        );
        let x_k = inst_tm_motive(
            m_tm,
            (1, 3, 1),
            Level::Zero,
            g_ctx(2),
            Type::Nat,
            Term::BoxTm(Rc::new(gtm(0, &g_ctx(2)))),
            &gt,
        );
        let code = Type::Vec {
            level: lvar(0),
            elem: Rc::new(gty(1, &g_ctx(2))),
            len: Rc::new(gtm(0, &g_ctx(2))),
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
                        ty: Rc::new(Type::Nat),
                        level: Level::Zero,
                        body: None,
                    },
                ],
                locals: vec![
                    (Rc::new(x_t), l1.shift(1, 0)),
                    (Rc::new(x_k), l2.shift(1, 0)),
                ],
            },
            ty: Rc::new(inst_ty_motive(
                m_ty,
                (1, 3, 2),
                lvar(0),
                g_ctx(2),
                Term::BoxTy(Rc::new(code)),
                &gt,
            )),
            level: l1.shift(1, 0),
        }
    };

    // (ℓ, g, u_t : Trm_c(g ⊢ Ty ℓ @ 1+ℓ), u_k : Trm_c(g ⊢ Nat @ 0),
    //  x_t, x_k. t'_Vec)
    //   : M_Trm[1+ℓ/ℓ, g/g, Ty ℓ/U_T, box (Vec^ℓ(u_t^id; u_k^id))/x_t]
    let tm_vec = {
        let gt = gt(1, 3);
        // telescope view: g = 2, u_t = 1, u_k = 0
        let x_t = inst_tm_motive(
            m_tm,
            (1, 3, 0),
            Level::succ(lvar(0)),
            g_ctx(2),
            Type::Ty(lvar(0)),
            Term::BoxTm(Rc::new(gtm(1, &g_ctx(2)))),
            &gt,
        );
        let x_k = inst_tm_motive(
            m_tm,
            (1, 3, 1),
            Level::Zero,
            g_ctx(2),
            Type::Nat,
            Term::BoxTm(Rc::new(gtm(0, &g_ctx(2)))),
            &gt,
        );
        let code = Term::TmVec {
            level: lvar(0),
            elem: Rc::new(gtm(1, &g_ctx(2))),
            len: Rc::new(gtm(0, &g_ctx(2))),
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
                        body: None,
                    },
                    GlobalBinding::Tm {
                        ctx: g_ctx(1),
                        layer: Layer::Code,
                        ty: Rc::new(Type::Nat),
                        level: Level::Zero,
                        body: None,
                    },
                ],
                locals: vec![
                    (Rc::new(x_t), l2.shift(1, 0)),
                    (Rc::new(x_k), l2.shift(1, 0)),
                ],
            },
            ty: Rc::new(inst_tm_motive(
                m_tm,
                (1, 3, 2),
                Level::succ(lvar(0)),
                g_ctx(2),
                Type::Ty(lvar(0)),
                Term::BoxTm(Rc::new(code)),
                &gt,
            )),
            level: l2.shift(1, 0),
        }
    };

    // (g, u_k : Trm_c(g ⊢ Nat @ 0), x_k. t_Fin)
    //   : M_Typ[0/ℓ, g/g, box Fin(u_k^id)/x_T] — no universe binder: `Fin`
    // lives at 0 whatever its length.
    let ty_fin = {
        let gt = gt(0, 2);
        // telescope view: g = 1, u_k = 0
        let x_k = inst_tm_motive(
            m_tm,
            (0, 2, 0),
            Level::Zero,
            g_ctx(1),
            Type::Nat,
            Term::BoxTm(Rc::new(gtm(0, &g_ctx(1)))),
            &gt,
        );
        let code = Type::Fin { len: Rc::new(gtm(0, &g_ctx(1))) };
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
                        body: None,
                    },
                ],
                locals: vec![(Rc::new(x_k), l2.clone())],
            },
            ty: Rc::new(inst_ty_motive(
                m_ty,
                (0, 2, 1),
                Level::Zero,
                g_ctx(1),
                Term::BoxTy(Rc::new(code)),
                &gt,
            )),
            level: l1.clone(),
        }
    };

    // (g, u_k : Trm_c(g ⊢ Nat @ 0), x_k. t'_Fin)
    //   : M_Trm[1/ℓ, g/g, Ty 0/U_T, box (Fin u_k^id)/x_t]
    let tm_fin = {
        let gt = gt(0, 2);
        let x_k = inst_tm_motive(
            m_tm,
            (0, 2, 0),
            Level::Zero,
            g_ctx(1),
            Type::Nat,
            Term::BoxTm(Rc::new(gtm(0, &g_ctx(1)))),
            &gt,
        );
        let code = Term::TmFin { len: Rc::new(gtm(0, &g_ctx(1))) };
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
                        body: None,
                    },
                ],
                locals: vec![(Rc::new(x_k), l2.clone())],
            },
            ty: Rc::new(inst_tm_motive(
                m_tm,
                (0, 2, 1),
                Level::constant(1),
                g_ctx(1),
                Type::Ty(Level::Zero),
                Term::BoxTm(Rc::new(code)),
                &gt,
            )),
            level: l2.clone(),
        }
    };

    // (ℓ, g, U_S : Typ_c(g, ℓ), u_n : Trm_c((g, x : U_S^id @ ℓ) ⊢ Nat @ 0),
    //  x_S, x_n. t_Wf) : M_Typ[ℓ/ℓ, g/g, box (Wf^ℓ(x:U_S^id). u_n^id)/x_T]
    // Mirrors ty_w, but the positions are an arity *term*, so only one
    // universe is bound and the result level is ℓ itself.
    let ty_wf = {
        let gt = gt(1, 3);
        // telescope view: g = 2, U_S = 1, u_n = 0
        let gx = ext_ctx(&g_ctx(2), gty(1, &g_ctx(2)), lvar(0));
        let x_s = inst_ty_motive(
            m_ty,
            (1, 3, 0),
            lvar(0),
            g_ctx(2),
            Term::BoxTy(Rc::new(gty(1, &g_ctx(2)))),
            &gt,
        );
        let x_n = inst_tm_motive(
            m_tm,
            (1, 3, 1),
            Level::Zero,
            gx.clone(),
            Type::Nat,
            Term::BoxTm(Rc::new(gtm(0, &gx))),
            &gt,
        );
        let code = Type::Wf {
            level: lvar(0),
            shape: Rc::new(gty(1, &g_ctx(2))),
            arity: Rc::new(gtm(0, &gx)),
        };
        BranchSpec {
            tele: Tele {
                univs: 1,
                globals: vec![
                    GlobalBinding::Ctx,
                    GlobalBinding::Ty { ctx: g_ctx(0), layer: Layer::Code, level: lvar(0) },
                    GlobalBinding::Tm {
                        ctx: ext_ctx(&g_ctx(1), gty(0, &g_ctx(1)), lvar(0)),
                        layer: Layer::Code,
                        ty: Rc::new(Type::Nat),
                        level: Level::Zero,
                        body: None,
                    },
                ],
                locals: vec![
                    (Rc::new(x_s), l1.shift(1, 0)),
                    (Rc::new(x_n), l2.shift(1, 0)),
                ],
            },
            ty: Rc::new(inst_ty_motive(
                m_ty,
                (1, 3, 2),
                lvar(0),
                g_ctx(2),
                Term::BoxTy(Rc::new(code)),
                &gt,
            )),
            level: l1.shift(1, 0),
        }
    };

    // (ℓ, g, u_s : Trm_c(g ⊢ Ty ℓ @ 1+ℓ),
    //  u_n : Trm_c((g, x : El ℓ u_s^id @ ℓ) ⊢ Nat @ 0), x_s, x_n. t'_Wf)
    //   : M_Trm[1+ℓ/ℓ, g/g, Ty ℓ/U_T, box (Wf^ℓ(x:u_s^id). u_n^id)/x_t]
    let tm_wf = {
        let gt = gt(1, 3);
        // telescope view: g = 2, u_s = 1, u_n = 0
        let gx = ext_ctx(
            &g_ctx(2),
            Type::El { level: lvar(0), tm: Rc::new(gtm(1, &g_ctx(2))) },
            lvar(0),
        );
        let x_s = inst_tm_motive(
            m_tm,
            (1, 3, 0),
            Level::succ(lvar(0)),
            g_ctx(2),
            Type::Ty(lvar(0)),
            Term::BoxTm(Rc::new(gtm(1, &g_ctx(2)))),
            &gt,
        );
        let x_n = inst_tm_motive(
            m_tm,
            (1, 3, 1),
            Level::Zero,
            gx.clone(),
            Type::Nat,
            Term::BoxTm(Rc::new(gtm(0, &gx))),
            &gt,
        );
        let code = Term::TmWf {
            level: lvar(0),
            shape: Rc::new(gtm(1, &g_ctx(2))),
            arity: Rc::new(gtm(0, &gx)),
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
                        body: None,
                    },
                    GlobalBinding::Tm {
                        ctx: ext_ctx(
                            &g_ctx(1),
                            Type::El { level: lvar(0), tm: Rc::new(gtm(0, &g_ctx(1))) },
                            lvar(0),
                        ),
                        layer: Layer::Code,
                        ty: Rc::new(Type::Nat),
                        level: Level::Zero,
                        body: None,
                    },
                ],
                locals: vec![
                    (Rc::new(x_s), l2.shift(1, 0)),
                    (Rc::new(x_n), l2.shift(1, 0)),
                ],
            },
            ty: Rc::new(inst_tm_motive(
                m_tm,
                (1, 3, 2),
                Level::succ(lvar(0)),
                g_ctx(2),
                Type::Ty(lvar(0)),
                Term::BoxTm(Rc::new(code)),
                &gt,
            )),
            level: l2.shift(1, 0),
        }
    };

    // (ℓ, g, U_S : Typ_c(g, ℓ), u_n : Trm_c((g, x : U_S^id @ ℓ) ⊢ Nat @ 0),
    //  u_a : Trm_c(g ⊢ U_S^id @ ℓ),
    //  u_cs : Trm_c(g ⊢ Vec^ℓ(Wf^ℓ(x:U_S^id).u_n^id; u_n^{id,u_a/x}) @ ℓ),
    //  x_S, x_n, x_a, x_cs. t_supf)
    //   : M_Trm[ℓ/ℓ, g/g, Wf^ℓ(x:U_S^id).u_n^id / U_T,
    //           box (sup_f(x:U_S^id. u_n^id; u_a^id; u_cs^id))/x_t]
    // The `tm_sup` analogue with the child function replaced by a tuple.
    let tm_supf = {
        let gt = gt(1, 5);
        // telescope view: g = 4, U_S = 3, u_n = 2, u_a = 1, u_cs = 0
        let g4 = g_ctx(4);
        let gx = ext_ctx(&g4, gty(3, &g4), lvar(0));
        let wf4 = Type::Wf {
            level: lvar(0),
            shape: Rc::new(gty(3, &g4)),
            arity: Rc::new(gtm(2, &gx)),
        };
        // u_n^{id, u_a/x} — the arity at the label.
        let arity_at = Term::GlobalTm {
            var: GlobalVar::index(2),
            subst: LocalSubst::id(&g4).extended(Rc::new(gtm(1, &g4))),
        };
        let cs_ty = Type::Vec {
            level: lvar(0),
            elem: Rc::new(wf4.clone()),
            len: Rc::new(arity_at),
        };
        let x_s = inst_ty_motive(
            m_ty,
            (1, 5, 0),
            lvar(0),
            g4.clone(),
            Term::BoxTy(Rc::new(gty(3, &g4))),
            &gt,
        );
        let x_n = inst_tm_motive(
            m_tm,
            (1, 5, 1),
            Level::Zero,
            gx.clone(),
            Type::Nat,
            Term::BoxTm(Rc::new(gtm(2, &gx))),
            &gt,
        );
        let x_a = inst_tm_motive(
            m_tm,
            (1, 5, 2),
            lvar(0),
            g4.clone(),
            gty(3, &g4),
            Term::BoxTm(Rc::new(gtm(1, &g4))),
            &gt,
        );
        let x_cs = inst_tm_motive(
            m_tm,
            (1, 5, 3),
            lvar(0),
            g4.clone(),
            cs_ty,
            Term::BoxTm(Rc::new(gtm(0, &g4))),
            &gt,
        );
        let code = Term::Supf {
            level: lvar(0),
            shape: Rc::new(gty(3, &g4)),
            arity: Rc::new(gtm(2, &gx)),
            label: Rc::new(gtm(1, &g4)),
            children: Rc::new(gtm(0, &g4)),
        };
        // u_cs's binding type, prefix (g, U_S, u_n, u_a): g=3, U_S=2, u_n=1,
        // u_a=0.
        let g3 = g_ctx(3);
        let gx3 = ext_ctx(&g3, gty(2, &g3), lvar(0));
        let wf3 = Type::Wf {
            level: lvar(0),
            shape: Rc::new(gty(2, &g3)),
            arity: Rc::new(gtm(1, &gx3)),
        };
        let arity_at3 = Term::GlobalTm {
            var: GlobalVar::index(1),
            subst: LocalSubst::id(&g3).extended(Rc::new(gtm(0, &g3))),
        };
        let cs_ty_bind = Type::Vec {
            level: lvar(0),
            elem: Rc::new(wf3),
            len: Rc::new(arity_at3),
        };
        BranchSpec {
            tele: Tele {
                univs: 1,
                globals: vec![
                    GlobalBinding::Ctx,
                    GlobalBinding::Ty { ctx: g_ctx(0), layer: Layer::Code, level: lvar(0) },
                    GlobalBinding::Tm {
                        ctx: ext_ctx(&g_ctx(1), gty(0, &g_ctx(1)), lvar(0)),
                        layer: Layer::Code,
                        ty: Rc::new(Type::Nat),
                        level: Level::Zero,
                        body: None,
                    },
                    GlobalBinding::Tm {
                        ctx: g_ctx(2),
                        layer: Layer::Code,
                        ty: Rc::new(gty(1, &g_ctx(2))),
                        level: lvar(0),
                        body: None,
                    },
                    GlobalBinding::Tm {
                        ctx: g_ctx(3),
                        layer: Layer::Code,
                        ty: Rc::new(cs_ty_bind),
                        level: lvar(0),
                        body: None,
                    },
                ],
                locals: vec![
                    (Rc::new(x_s), l1.shift(1, 0)),
                    (Rc::new(x_n), l2.shift(1, 0)),
                    (Rc::new(x_a), l2.shift(1, 0)),
                    (Rc::new(x_cs), l2.shift(1, 0)),
                ],
            },
            ty: Rc::new(inst_tm_motive(
                m_tm,
                (1, 5, 4),
                lvar(0),
                g4,
                wf4,
                Term::BoxTm(Rc::new(code)),
                &gt,
            )),
            level: l2.shift(1, 0),
        }
    };

    // (ℓ, ℓ', g, U_S : Typ_c(g, ℓ),
    //  u_n : Trm_c((g, x : U_S^id @ ℓ) ⊢ Nat @ 0),
    //  U_M : Typ_c((g, z : Wf^ℓ(x:U_S^id).u_n^id @ ℓ), ℓ'),
    //  u_s : Trm_c((g, a, cs, ih) ⊢ U_M^{id, sup_f(a; cs)/z} @ ℓ'),
    //  u_t : Trm_c(g ⊢ Wf^ℓ(x:U_S^id).u_n^id @ ℓ),
    //  x_S, x_n, x_M, x_s, x_t. t_elimWf)
    //   : M_Trm[ℓ'/ℓ, g/g, U_M^{id, u_t^id/z}/U_T,
    //           box (elim_Wf (x. U_S^id. u_n^id) (z. U_M^id)
    //                (a cs ih. u_s^id) u_t^id)/x_t]
    // The step telescope comes from `wf_step_telescope`, exactly as in the
    // typing rule; x_M is at the *type* motive. Mirrors tm_elim_w.
    let tm_elim_wf = {
        let gt = gt(2, 6);
        // telescope view: g = 5, U_S = 4, u_n = 3, U_M = 2, u_s = 1, u_t = 0.
        // Univs: ℓ = lvar(1), ℓ' = lvar(0).
        let g5 = g_ctx(5);
        let gx = ext_ctx(&g5, gty(4, &g5), lvar(1));
        let shape5 = Rc::new(gty(4, &g5));
        let arity5 = Rc::new(gtm(3, &gx));
        let wf5 = Type::Wf {
            level: lvar(1),
            shape: Rc::clone(&shape5),
            arity: Rc::clone(&arity5),
        };
        let gz = ext_ctx(&g5, wf5.clone(), lvar(1));
        let motive5 = Rc::new(gty(2, &gz));
        let (cs_ty, ih_ty, step_ty) =
            wf_step_telescope(&g5, &lvar(1), &lvar(0), &shape5, &arity5, &motive5);
        let ga = ext_ctx(&g5, gty(4, &g5), lvar(1));
        let gacs = ext_ctx(&ga, cs_ty, lvar(1));
        let gacsi = ext_ctx(&gacs, ih_ty, lvar(0));
        let x_s = inst_ty_motive(
            m_ty,
            (2, 6, 0),
            lvar(1),
            g5.clone(),
            Term::BoxTy(Rc::new(gty(4, &g5))),
            &gt,
        );
        let x_n = inst_tm_motive(
            m_tm,
            (2, 6, 1),
            Level::Zero,
            gx.clone(),
            Type::Nat,
            Term::BoxTm(Rc::new(gtm(3, &gx))),
            &gt,
        );
        let x_m = inst_ty_motive(
            m_ty,
            (2, 6, 2),
            lvar(0),
            gz.clone(),
            Term::BoxTy(Rc::new(gty(2, &gz))),
            &gt,
        );
        let x_step = inst_tm_motive(
            m_tm,
            (2, 6, 3),
            lvar(0),
            gacsi.clone(),
            step_ty,
            Term::BoxTm(Rc::new(gtm(1, &gacsi))),
            &gt,
        );
        let x_scrut = inst_tm_motive(
            m_tm,
            (2, 6, 4),
            lvar(1),
            g5.clone(),
            wf5,
            Term::BoxTm(Rc::new(gtm(0, &g5))),
            &gt,
        );
        let code = Term::ElimWf {
            level: lvar(1),
            motive_level: lvar(0),
            shape: Rc::clone(&shape5),
            arity: Rc::clone(&arity5),
            motive: Rc::clone(&motive5),
            step: Rc::new(gtm(1, &gacsi)),
            scrut: Rc::new(gtm(0, &g5)),
        };
        let u_m_at_scrut = Type::GlobalTy {
            var: GlobalVar::index(2),
            subst: LocalSubst::id(&g5).extended(Rc::new(gtm(0, &g5))),
        };
        // -- global bindings, each scoped in its own Ψ-prefix --
        // U_M's context (g, z : Wf), prefix (g, U_S, u_n): g=2, U_S=1, u_n=0.
        let g2 = g_ctx(2);
        let gx2 = ext_ctx(&g2, gty(1, &g2), lvar(1));
        let wf2 = Type::Wf {
            level: lvar(1),
            shape: Rc::new(gty(1, &g2)),
            arity: Rc::new(gtm(0, &gx2)),
        };
        // u_s's binding, prefix (g, U_S, u_n, U_M): g=3, U_S=2, u_n=1, U_M=0.
        let g3 = g_ctx(3);
        let gx3 = ext_ctx(&g3, gty(2, &g3), lvar(1));
        let shape3 = Rc::new(gty(2, &g3));
        let arity3 = Rc::new(gtm(1, &gx3));
        let wf3 = Type::Wf {
            level: lvar(1),
            shape: Rc::clone(&shape3),
            arity: Rc::clone(&arity3),
        };
        let gz3 = ext_ctx(&g3, wf3, lvar(1));
        let motive3 = Rc::new(gty(0, &gz3));
        let (cs_ty3, ih_ty3, step_ty3) =
            wf_step_telescope(&g3, &lvar(1), &lvar(0), &shape3, &arity3, &motive3);
        let ga3 = ext_ctx(&g3, gty(2, &g3), lvar(1));
        let gacs3 = ext_ctx(&ga3, cs_ty3, lvar(1));
        let gacsi3 = ext_ctx(&gacs3, ih_ty3, lvar(0));
        // u_t's binding, prefix (g, U_S, u_n, U_M, u_s): g=4, U_S=3, u_n=2.
        let g4 = g_ctx(4);
        let gx4 = ext_ctx(&g4, gty(3, &g4), lvar(1));
        let wf4 = Type::Wf {
            level: lvar(1),
            shape: Rc::new(gty(3, &g4)),
            arity: Rc::new(gtm(2, &gx4)),
        };
        BranchSpec {
            tele: Tele {
                univs: 2,
                globals: vec![
                    GlobalBinding::Ctx,
                    GlobalBinding::Ty { ctx: g_ctx(0), layer: Layer::Code, level: lvar(1) },
                    GlobalBinding::Tm {
                        ctx: ext_ctx(&g_ctx(1), gty(0, &g_ctx(1)), lvar(1)),
                        layer: Layer::Code,
                        ty: Rc::new(Type::Nat),
                        level: Level::Zero,
                        body: None,
                    },
                    GlobalBinding::Ty {
                        ctx: ext_ctx(&g2, wf2, lvar(1)),
                        layer: Layer::Code,
                        level: lvar(0),
                    },
                    GlobalBinding::Tm {
                        ctx: gacsi3,
                        layer: Layer::Code,
                        ty: Rc::new(step_ty3),
                        level: lvar(0),
                        body: None,
                    },
                    GlobalBinding::Tm {
                        ctx: g4,
                        layer: Layer::Code,
                        ty: Rc::new(wf4),
                        level: lvar(1),
                        body: None,
                    },
                ],
                locals: vec![
                    (Rc::new(x_s), l1.shift(2, 0)),
                    (Rc::new(x_n), l2.shift(2, 0)),
                    (Rc::new(x_m), l1.shift(2, 0)),
                    (Rc::new(x_step), l2.shift(2, 0)),
                    (Rc::new(x_scrut), l2.shift(2, 0)),
                ],
            },
            ty: Rc::new(inst_tm_motive(
                m_tm,
                (2, 6, 5),
                lvar(0),
                g5,
                u_m_at_scrut,
                Term::BoxTm(Rc::new(code)),
                &gt,
            )),
            level: l2.shift(2, 0),
        }
    };

    // -- strict equality (extension; docs/kernel/sprop-design.md §6) ---------------

    // (ℓ, g, U_S : Typ_c(g, ℓ), u_t : Trm_c(g ⊢ U_S^id @ ℓ),
    //  u_u : Trm_c(g ⊢ U_S^id @ ℓ), x_S, x_t, x_u. t_sEq)
    //   : M_Typ[ℓ/ℓ, g/g, box (sEq^ℓ(U_S^id; u_t^id; u_u^id))/x_T]
    // Mirrors ty_id: sEq is Id minus relevance, and the code recursor is
    // structural on syntax.
    let ty_seq = {
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
        let code = Type::SEq {
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
                        body: None,
                    },
                    GlobalBinding::Tm {
                        ctx: g_ctx(2),
                        layer: Layer::Code,
                        ty: Rc::new(gty(1, &g_ctx(2))),
                        level: lvar(0),
                        body: None,
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

    // (ℓ, g, u_S, u_t, u_u, x_S, x_t, x_u. t'_sEq) — the encoding; mirrors
    // tm_id.
    let tm_seq = {
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
        let code = Term::TmSEq {
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
                        body: None,
                    },
                    GlobalBinding::Tm {
                        ctx: g_ctx(1),
                        layer: Layer::Code,
                        ty: Rc::new(Type::El {
                            level: lvar(0),
                            tm: Rc::new(gtm(0, &g_ctx(1))),
                        }),
                        level: lvar(0),
                        body: None,
                    },
                    GlobalBinding::Tm {
                        ctx: g_ctx(2),
                        layer: Layer::Code,
                        ty: Rc::new(Type::El {
                            level: lvar(0),
                            tm: Rc::new(gtm(1, &g_ctx(2))),
                        }),
                        level: lvar(0),
                        body: None,
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

    // (ℓ, g. t_sEmpty) : M_Typ[ℓ/ℓ, g/g, box sEmpty^ℓ/x_T] — mirrors
    // ty_empty.
    let ty_sempty = {
        let gt = gt(1, 1);
        BranchSpec {
            tele: Tele { univs: 1, globals: vec![GlobalBinding::Ctx], locals: vec![] },
            ty: Rc::new(inst_ty_motive(
                m_ty,
                (1, 1, 0),
                lvar(0),
                g_ctx(0),
                Term::BoxTy(Rc::new(Type::SEmpty { level: lvar(0) })),
                &gt,
            )),
            level: l1.shift(1, 0),
        }
    };

    // (ℓ, g. t'_sEmpty) : M_Trm[ℓ, g, Ty ℓ/U_T, box sEmpty^ℓ/x_t] — mirrors
    // tm_empty.
    let tm_sempty = {
        let gt = gt(1, 1);
        BranchSpec {
            tele: Tele { univs: 1, globals: vec![GlobalBinding::Ctx], locals: vec![] },
            ty: Rc::new(inst_tm_motive(
                m_tm,
                (1, 1, 0),
                Level::succ(lvar(0)),
                g_ctx(0),
                Type::Ty(lvar(0)),
                Term::BoxTm(Rc::new(Term::TmSEmpty { level: lvar(0) })),
                &gt,
            )),
            level: l2.shift(1, 0),
        }
    };

    // (ℓ, g, U_S : Typ_c(g, ℓ), u_t : Trm_c(g ⊢ U_S^id @ ℓ), x_S, x_t.
    //  t_srefl)
    //   : M_Trm[ℓ/ℓ, g/g, sEq^ℓ(U_S^id; u_t^id; u_t^id)/U_T,
    //           box (srefl^ℓ(U_S^id; u_t^id))/x_t]
    // Mirrors tm_refl.
    let tm_srefl = {
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
        let code = Term::SRefl {
            level: lvar(0),
            ty: Rc::new(gty(1, &g_ctx(2))),
            tm: Rc::new(gtm(0, &g_ctx(2))),
        };
        let seq_ty = Type::SEq {
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
                        body: None,
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
                seq_ty,
                Term::BoxTm(Rc::new(code)),
                &gt,
            )),
            level: l2.shift(1, 0),
        }
    };

    // (ℓ, ℓ', g, U_M : Typ_c((g, x : sEmpty^{ℓ'} @ ℓ'), ℓ),
    //  u_t : Trm_c(g ⊢ sEmpty^{ℓ'} @ ℓ'), x_M, x_t. t_elim_sE)
    //   : M_Trm[ℓ/ℓ, g/g, U_M^{id, u_t^id/x}/U_T, box (elim_sEmpty …)/x_t]
    // Mirrors tm_elim_empty, second universe included (sEmpty is
    // level-indexed).
    let tm_elim_sempty = {
        let gt = gt(2, 3);
        // telescope view: ℓ = 1 (motive), ℓ' = 0 (scrutinee); g = 2,
        // U_M = 1, u_t = 0
        let sempty = Type::SEmpty { level: lvar(0) };
        let gx = ext_ctx(&g_ctx(2), sempty.clone(), lvar(0));
        let motive_code = Type::GlobalTy { var: GlobalVar::index(1), subst: LocalSubst::id(&gx) };
        let x_m = inst_ty_motive(
            m_ty,
            (2, 3, 0),
            lvar(1),
            gx.clone(),
            Term::BoxTy(Rc::new(motive_code.clone())),
            &gt,
        );
        // Scrutinee's call at the scrutinee's level ℓ' (as `tm_elim_empty`).
        let x_t = inst_tm_motive(
            m_tm,
            (2, 3, 1),
            lvar(0),
            g_ctx(2),
            sempty.clone(),
            Term::BoxTm(Rc::new(gtm(0, &g_ctx(2)))),
            &gt,
        );
        let code = Term::ElimSEmpty {
            level: lvar(1),
            scrut_level: lvar(0),
            motive: Rc::new(motive_code),
            scrut: Rc::new(gtm(0, &g_ctx(2))),
        };
        let u_m_at_scrut = Type::GlobalTy {
            var: GlobalVar::index(1),
            subst: LocalSubst::id(&g_ctx(2)).extended(Rc::new(gtm(0, &g_ctx(2)))),
        };
        BranchSpec {
            tele: Tele {
                univs: 2,
                globals: vec![
                    GlobalBinding::Ctx,
                    GlobalBinding::Ty {
                        ctx: ext_ctx(&g_ctx(0), Type::SEmpty { level: lvar(0) }, lvar(0)),
                        layer: Layer::Code,
                        level: lvar(1),
                    },
                    GlobalBinding::Tm {
                        ctx: g_ctx(1),
                        layer: Layer::Code,
                        ty: Rc::new(Type::SEmpty { level: lvar(0) }),
                        level: lvar(0),
                        body: None,
                    },
                ],
                locals: vec![
                    (Rc::new(x_m), l1.shift(2, 0)),
                    (Rc::new(x_t), l2.shift(2, 0)),
                ],
            },
            ty: Rc::new(inst_tm_motive(
                m_tm,
                (2, 3, 2),
                lvar(1),
                g_ctx(2),
                u_m_at_scrut,
                Term::BoxTm(Rc::new(code)),
                &gt,
            )),
            level: l2.shift(2, 0),
        }
    };

    // -- propositional truncation (issues/sprop-squash.md) -----------------

    let ty_squash = {
        let gt = gt(1, 2);
        let x_a = inst_ty_motive(
            m_ty,
            (1, 2, 0),
            lvar(0),
            g_ctx(1),
            Term::BoxTy(Rc::new(gty(0, &g_ctx(1)))),
            &gt,
        );
        let code = Type::Squash { level: lvar(0), ty: Rc::new(gty(0, &g_ctx(1))) };
        BranchSpec {
            tele: Tele {
                univs: 1,
                globals: vec![
                    GlobalBinding::Ctx,
                    GlobalBinding::Ty { ctx: g_ctx(0), layer: Layer::Code, level: lvar(0) },
                ],
                locals: vec![(Rc::new(x_a), l1.shift(1, 0))],
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

    let tm_squash = {
        let gt = gt(1, 2);
        let x_a = inst_tm_motive(
            m_tm,
            (1, 2, 0),
            Level::succ(lvar(0)),
            g_ctx(1),
            Type::Ty(lvar(0)),
            Term::BoxTm(Rc::new(gtm(0, &g_ctx(1)))),
            &gt,
        );
        let code = Term::TmSquash { level: lvar(0), ty: Rc::new(gtm(0, &g_ctx(1))) };
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
                        body: None,
                    },
                ],
                locals: vec![(Rc::new(x_a), l2.shift(1, 0))],
            },
            ty: Rc::new(inst_tm_motive(
                m_tm,
                (1, 2, 1),
                Level::succ(lvar(0)),
                g_ctx(1),
                Type::Ty(lvar(0)),
                Term::BoxTm(Rc::new(code)),
                &gt,
            )),
            level: l2.shift(1, 0),
        }
    };

    let tm_squash_in = {
        let gt = gt(1, 3);
        let x_a = inst_ty_motive(
            m_ty,
            (1, 3, 0),
            lvar(0),
            g_ctx(2),
            Term::BoxTy(Rc::new(gty(1, &g_ctx(2)))),
            &gt,
        );
        let x_tm = inst_tm_motive(
            m_tm,
            (1, 3, 1),
            lvar(0),
            g_ctx(2),
            gty(1, &g_ctx(2)),
            Term::BoxTm(Rc::new(gtm(0, &g_ctx(2)))),
            &gt,
        );
        let sq_ty = Type::Squash { level: lvar(0), ty: Rc::new(gty(1, &g_ctx(2))) };
        let code = Term::Squash {
            level: lvar(0),
            ty: Rc::new(gty(1, &g_ctx(2))),
            tm: Rc::new(gtm(0, &g_ctx(2))),
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
                        body: None,
                    },
                ],
                locals: vec![
                    (Rc::new(x_a), l1.shift(1, 0)),
                    (Rc::new(x_tm), l2.shift(1, 0)),
                ],
            },
            ty: Rc::new(inst_tm_motive(
                m_tm,
                (1, 3, 2),
                lvar(0),
                g_ctx(2),
                sq_ty,
                Term::BoxTm(Rc::new(code)),
                &gt,
            )),
            level: l2.shift(1, 0),
        }
    };

    let tm_elim_squash = {
        let gt = gt(2, 5);
        // Final telescope: g=4, U_A=3, U_B=2, u_b=1, u_q=0.
        let a4 = gty(3, &g_ctx(4));
        let sq_a4 = Type::Squash { level: lvar(1), ty: Rc::new(a4.clone()) };
        let gz4 = ext_ctx(&g_ctx(4), sq_a4.clone(), lvar(1));
        let gx4 = ext_ctx(&g_ctx(4), a4.clone(), lvar(1));
        let motive_code = Type::GlobalTy { var: GlobalVar::index(2), subst: LocalSubst::id(&gz4) };
        let packed_x = Term::Squash {
            level: lvar(1),
            ty: Rc::new(a4.shift_local(1)),
            tm: Rc::new(Term::Var(LocalVar(0))),
        };
        let b_at_x = Type::GlobalTy {
            var: GlobalVar::index(2),
            subst: LocalSubst::id(&g_ctx(4)).shift_local(1).extended(Rc::new(packed_x)),
        };
        let branch_ty = Type::Squash { level: lvar(0), ty: Rc::new(b_at_x) };
        let result_inner = Type::GlobalTy {
            var: GlobalVar::index(2),
            subst: LocalSubst::id(&g_ctx(4)).extended(Rc::new(gtm(0, &g_ctx(4)))),
        };
        let result_ty = Type::Squash { level: lvar(0), ty: Rc::new(result_inner) };

        let x_a = inst_ty_motive(
            m_ty,
            (2, 5, 0),
            lvar(1),
            g_ctx(4),
            Term::BoxTy(Rc::new(a4.clone())),
            &gt,
        );
        let x_b = inst_ty_motive(
            m_ty,
            (2, 5, 1),
            lvar(0),
            gz4.clone(),
            Term::BoxTy(Rc::new(gty(2, &gz4))),
            &gt,
        );
        let x_case = inst_tm_motive(
            m_tm,
            (2, 5, 2),
            lvar(0),
            gx4.clone(),
            branch_ty.clone(),
            Term::BoxTm(Rc::new(gtm(1, &gx4))),
            &gt,
        );
        let x_q = inst_tm_motive(
            m_tm,
            (2, 5, 3),
            lvar(1),
            g_ctx(4),
            sq_a4.clone(),
            Term::BoxTm(Rc::new(gtm(0, &g_ctx(4)))),
            &gt,
        );
        let code = Term::ElimSquash {
            src_level: lvar(1),
            dst_level: lvar(0),
            src_ty: Rc::new(a4),
            motive: Rc::new(motive_code),
            case: Rc::new(gtm(1, &gx4)),
            scrut: Rc::new(gtm(0, &g_ctx(4))),
        };

        // Prefix-scoped global types.
        let a1 = gty(0, &g_ctx(1));
        let sq_a1 = Type::Squash { level: lvar(1), ty: Rc::new(a1.clone()) };
        let gz1 = ext_ctx(&g_ctx(1), sq_a1, lvar(1));
        let gx2 = ext_ctx(&g_ctx(2), gty(1, &g_ctx(2)), lvar(1));
        let packed_bind = Term::Squash {
            level: lvar(1),
            ty: Rc::new(gty(1, &g_ctx(2)).shift_local(1)),
            tm: Rc::new(Term::Var(LocalVar(0))),
        };
        let b_bind = Type::GlobalTy {
            var: GlobalVar::index(0),
            subst: LocalSubst::id(&g_ctx(2)).shift_local(1).extended(Rc::new(packed_bind)),
        };
        let q_ty = Type::Squash { level: lvar(1), ty: Rc::new(gty(2, &g_ctx(3))) };
        BranchSpec {
            tele: Tele {
                univs: 2,
                globals: vec![
                    GlobalBinding::Ctx,
                    GlobalBinding::Ty { ctx: g_ctx(0), layer: Layer::Code, level: lvar(1) },
                    GlobalBinding::Ty { ctx: gz1, layer: Layer::Code, level: lvar(0) },
                    GlobalBinding::Tm {
                        ctx: gx2,
                        layer: Layer::Code,
                        ty: Rc::new(Type::Squash { level: lvar(0), ty: Rc::new(b_bind) }),
                        level: lvar(0),
                        body: None,
                    },
                    GlobalBinding::Tm {
                        ctx: g_ctx(3),
                        layer: Layer::Code,
                        ty: Rc::new(q_ty),
                        level: lvar(1),
                        body: None,
                    },
                ],
                locals: vec![
                    (Rc::new(x_a), l1.shift(2, 0)),
                    (Rc::new(x_b), l1.shift(2, 0)),
                    (Rc::new(x_case), l2.shift(2, 0)),
                    (Rc::new(x_q), l2.shift(2, 0)),
                ],
            },
            ty: Rc::new(inst_tm_motive(
                m_tm,
                (2, 5, 4),
                lvar(0),
                g_ctx(4),
                result_ty,
                Term::BoxTm(Rc::new(code)),
                &gt,
            )),
            level: l2.shift(2, 0),
        }
    };

    // -- M (docs/kernel/kernel-m-codes-design.md §2) -------------------------------
    //
    // Univs `l, l', li` (and `k` for corec) are pushed in that order, so the
    // innermost is `li` (or `k`). Every branch opens with the signature's
    // five globals `g, I, S, P, o` ([`m_sig_globals`]); `x_I … x_o` are its
    // recursive results, each at the motive over the context its piece lives
    // in.
    let m_sig_locals = |coded: bool, univs: u32, tg: u32, v: &MView, gt: &LocalCtx| {
        let sig = &v.sig;
        let (l, lp, li) = (&sig.level, &sig.pos_level, &sig.idx_level);
        let k = tg - 5;
        if coded {
            let piece = |var: u32, ctx: &LocalCtx, level: &Level, at: u32| {
                inst_tm_motive(
                    m_tm,
                    (univs, tg, at),
                    Level::succ(level.clone()),
                    ctx.clone(),
                    Type::Ty(level.clone()),
                    Term::BoxTm(Rc::new(gtm(var, ctx))),
                    gt,
                )
            };
            vec![
                (Rc::new(piece(k + 3, &v.g, li, 0)), l2.shift(univs, 0)),
                (Rc::new(piece(k + 2, &v.gi, l, 1)), l2.shift(univs, 0)),
                (Rc::new(piece(k + 1, &v.gis, lp, 2)), l2.shift(univs, 0)),
                (
                    Rc::new(inst_tm_motive(
                        m_tm,
                        (univs, tg, 3),
                        li.clone(),
                        v.gisp.clone(),
                        sig.idx.shift_local(3),
                        Term::BoxTm(Rc::clone(&sig.next)),
                        gt,
                    )),
                    l2.shift(univs, 0),
                ),
            ]
        } else {
            let piece = |ty: &Rc<Type>, ctx: &LocalCtx, level: &Level, at: u32| {
                inst_ty_motive(m_ty, (univs, tg, at), level.clone(), ctx.clone(), Term::BoxTy(Rc::clone(ty)), gt)
            };
            vec![
                (Rc::new(piece(&sig.idx, &v.g, li, 0)), l1.shift(univs, 0)),
                (Rc::new(piece(&sig.shape, &v.gi, l, 1)), l1.shift(univs, 0)),
                (Rc::new(piece(&sig.pos, &v.gis, lp, 2)), l1.shift(univs, 0)),
                (
                    Rc::new(inst_tm_motive(
                        m_tm,
                        (univs, tg, 3),
                        li.clone(),
                        v.gisp.clone(),
                        sig.idx.shift_local(3),
                        Term::BoxTm(Rc::clone(&sig.next)),
                        gt,
                    )),
                    l2.shift(univs, 0),
                ),
            ]
        }
    };

    // (l, l', li, g, U_I, U_S, U_P, u_o, u_j : Trm_c(g ⊢ U_I^id @ li),
    //  x_I, x_S, x_P, x_o, x_j. t_M)
    //   : M_Typ[l⊔l'⊔li/ℓ, g/g, box M(U_I; U_S; U_P; u_o)(u_j^id)/x_T]
    let (ty_m, tm_m) = {
        let make = |coded: bool| {
            let (l, lp, li) = (lvar(2), lvar(1), lvar(0));
            let gt = gt(3, 6);
            // Prefix of u_j: (g, I, S, P, o) — o at 0.
            let pre = m_view(coded, 0, &l, &lp, &li);
            let mut globals = m_sig_globals(coded, &l, &lp, &li);
            globals.push(GlobalBinding::Tm {
                ctx: pre.g.clone(),
                layer: Layer::Code,
                ty: Rc::clone(&pre.sig.idx),
                level: li.clone(),
                body: None,
            });
            // Telescope view: g = 5, I = 4, S = 3, P = 2, o = 1, j = 0.
            let v = m_view(coded, 1, &l, &lp, &li);
            let j = Rc::new(gtm(0, &v.g));
            let mut locals = m_sig_locals(coded, 3, 6, &v, &gt);
            locals.push((
                Rc::new(inst_tm_motive(
                    m_tm,
                    (3, 6, 4),
                    li.clone(),
                    v.g.clone(),
                    (*v.sig.idx).clone(),
                    Term::BoxTm(Rc::clone(&j)),
                    &gt,
                )),
                l2.shift(3, 0),
            ));
            let family = v.sig.family_level();
            let ty = if coded {
                let code = Term::TmM {
                    level: l.clone(),
                    pos_level: lp.clone(),
                    idx_level: li.clone(),
                    idx: Rc::new(gtm(4, &v.g)),
                    shape: Rc::new(gtm(3, &v.gi)),
                    pos: Rc::new(gtm(2, &v.gis)),
                    next: Rc::clone(&v.sig.next),
                    index: Rc::clone(&j),
                };
                inst_tm_motive(
                    m_tm,
                    (3, 6, 5),
                    Level::succ(family.clone()),
                    v.g.clone(),
                    Type::Ty(family),
                    Term::BoxTm(Rc::new(code)),
                    &gt,
                )
            } else {
                inst_ty_motive(
                    m_ty,
                    (3, 6, 5),
                    family,
                    v.g.clone(),
                    Term::BoxTy(Rc::new(v.sig.at(j))),
                    &gt,
                )
            };
            BranchSpec {
                tele: Tele { univs: 3, globals, locals },
                ty: Rc::new(ty),
                level: if coded { l2.shift(3, 0) } else { l1.shift(3, 0) },
            }
        };
        (make(false), make(true))
    };

    // (l, l', li, k, g, U_I, U_S, U_P, u_o, U_X : Typ_c((g, i : U_I), k),
    //  u_c : Trm_c((g, i, x : U_X) ⊢ step(σ, U_X) @ l⊔k⊔f),
    //  u_j : Trm_c(g ⊢ U_I), u_x : Trm_c(g ⊢ U_X[u_j/i] @ k),
    //  x_I, x_S, x_P, x_o, x_X, x_c, x_j, x_x. t_corec)
    //   : M_Trm[f/ℓ, g/g, M(σ)(u_j)/U_T, box corec^k(σ; U_X; u_c; u_j; u_x)/x_t]
    // with f = l ⊔ l' ⊔ li; the step type is `m_step_ty`, as in the typing
    // rule, never restated.
    let tm_corec = {
        let (l, lp, li, k) = (lvar(3), lvar(2), lvar(1), lvar(0));
        let gt = gt(4, 9);
        let step_level = |sig: &crate::term::MSig| Level::join(sig.level.clone(), Level::join(k.clone(), sig.family_level()));
        let mut globals = m_sig_globals(false, &l, &lp, &li);
        // U_X, prefix (g, I, S, P, o): o = 0.
        let v0 = m_view(false, 0, &l, &lp, &li);
        globals.push(GlobalBinding::Ty { ctx: v0.gi.clone(), layer: Layer::Code, level: k.clone() });
        // u_c, prefix (…, o, X): o = 1, X = 0.
        let v1 = m_view(false, 1, &l, &lp, &li);
        let x1 = gty(0, &v1.gi);
        globals.push(GlobalBinding::Tm {
            ctx: ext_ctx(&v1.gi, x1.clone(), k.clone()),
            layer: Layer::Code,
            ty: Rc::new(m_step_ty(&v1.sig, &k, &x1).shift_local(1)),
            level: step_level(&v1.sig),
            body: None,
        });
        // u_j, prefix (…, o, X, c): o = 2.
        let v2 = m_view(false, 2, &l, &lp, &li);
        globals.push(GlobalBinding::Tm {
            ctx: v2.g.clone(),
            layer: Layer::Code,
            ty: Rc::clone(&v2.sig.idx),
            level: li.clone(),
            body: None,
        });
        // u_x, prefix (…, o, X, c, j): o = 3, X = 2, j = 0.
        let v3 = m_view(false, 3, &l, &lp, &li);
        globals.push(GlobalBinding::Tm {
            ctx: v3.g.clone(),
            layer: Layer::Code,
            ty: Rc::new(gty(2, &v3.gi).inst_top(0, &gtm(0, &v3.g))),
            level: k.clone(),
            body: None,
        });
        // Telescope view: g = 8, I = 7, S = 6, P = 5, o = 4, X = 3, c = 2,
        // j = 1, x = 0.
        let v = m_view(false, 4, &l, &lp, &li);
        let carrier = Rc::new(gty(3, &v.gi));
        let gix = ext_ctx(&v.gi, (*carrier).clone(), k.clone());
        let step = Rc::new(gtm(2, &gix));
        let step_ty = m_step_ty(&v.sig, &k, &carrier).shift_local(1);
        let j = Rc::new(gtm(1, &v.g));
        let x = Rc::new(gtm(0, &v.g));
        let mut locals = m_sig_locals(false, 4, 9, &v, &gt);
        locals.push((
            Rc::new(inst_ty_motive(m_ty, (4, 9, 4), k.clone(), v.gi.clone(), Term::BoxTy(Rc::clone(&carrier)), &gt)),
            l1.shift(4, 0),
        ));
        locals.push((
            Rc::new(inst_tm_motive(m_tm, (4, 9, 5), step_level(&v.sig), gix.clone(), step_ty, Term::BoxTm(Rc::clone(&step)), &gt)),
            l2.shift(4, 0),
        ));
        locals.push((
            Rc::new(inst_tm_motive(m_tm, (4, 9, 6), li.clone(), v.g.clone(), (*v.sig.idx).clone(), Term::BoxTm(Rc::clone(&j)), &gt)),
            l2.shift(4, 0),
        ));
        locals.push((
            Rc::new(inst_tm_motive(
                m_tm,
                (4, 9, 7),
                k.clone(),
                v.g.clone(),
                carrier.inst_top(0, &j),
                Term::BoxTm(Rc::clone(&x)),
                &gt,
            )),
            l2.shift(4, 0),
        ));
        let code = Term::Corec {
            sig: Rc::clone(&v.sig),
            carrier_level: k.clone(),
            carrier: Rc::clone(&carrier),
            step,
            index: Rc::clone(&j),
            seed: x,
        };
        BranchSpec {
            tele: Tele { univs: 4, globals, locals },
            ty: Rc::new(inst_tm_motive(
                m_tm,
                (4, 9, 8),
                v.sig.family_level(),
                v.g.clone(),
                v.sig.at(Rc::clone(&j)),
                Term::BoxTm(Rc::new(code)),
                &gt,
            )),
            level: l2.shift(4, 0),
        }
    };

    // (l, l', li, g, U_I, U_S, U_P, u_o, u_j, u_m : Trm_c(g ⊢ M(σ)(u_j) @ f),
    //  x_I, x_S, x_P, x_o, x_j, x_m. t_out)
    //   : M_Trm[l⊔f/ℓ, g/g, Σ(s : S[u_j]). Π(p : P). M(σ)(o)/U_T,
    //           box out(σ; u_j; u_m)/x_t]
    let tm_out = {
        let (l, lp, li) = (lvar(2), lvar(1), lvar(0));
        let gt = gt(3, 7);
        let mut globals = m_sig_globals(false, &l, &lp, &li);
        let v0 = m_view(false, 0, &l, &lp, &li);
        globals.push(GlobalBinding::Tm {
            ctx: v0.g.clone(),
            layer: Layer::Code,
            ty: Rc::clone(&v0.sig.idx),
            level: li.clone(),
            body: None,
        });
        // u_m, prefix (…, o, j): o = 1, j = 0.
        let v1 = m_view(false, 1, &l, &lp, &li);
        globals.push(GlobalBinding::Tm {
            ctx: v1.g.clone(),
            layer: Layer::Code,
            ty: Rc::new(v1.sig.at(Rc::new(gtm(0, &v1.g)))),
            level: v1.sig.family_level(),
            body: None,
        });
        // Telescope view: g = 6, I = 5, S = 4, P = 3, o = 2, j = 1, m = 0.
        let v = m_view(false, 2, &l, &lp, &li);
        let j = Rc::new(gtm(1, &v.g));
        let m = Rc::new(gtm(0, &v.g));
        let family = v.sig.family_level();
        let mut locals = m_sig_locals(false, 3, 7, &v, &gt);
        locals.push((
            Rc::new(inst_tm_motive(m_tm, (3, 7, 4), li.clone(), v.g.clone(), (*v.sig.idx).clone(), Term::BoxTm(Rc::clone(&j)), &gt)),
            l2.shift(3, 0),
        ));
        locals.push((
            Rc::new(inst_tm_motive(
                m_tm,
                (3, 7, 5),
                family.clone(),
                v.g.clone(),
                v.sig.at(Rc::clone(&j)),
                Term::BoxTm(Rc::clone(&m)),
                &gt,
            )),
            l2.shift(3, 0),
        ));
        let code = Term::Out { sig: Rc::clone(&v.sig), index: Rc::clone(&j), scrut: m };
        BranchSpec {
            tele: Tele { univs: 3, globals, locals },
            ty: Rc::new(inst_tm_motive(
                m_tm,
                (3, 7, 6),
                Level::join(l.clone(), family),
                v.g.clone(),
                m_out_ty(&v.sig, &j),
                Term::BoxTm(Rc::new(code)),
                &gt,
            )),
            level: l2.shift(3, 0),
        }
    };

    // -- dependent tuples and indexed trees (docs/kernel/iwf-former-design.md §6) --
    //
    // heather-coq's M17c branches 55–60 (`RecSpec`: `brDecls`, `br_calls`,
    // `br_head`), checked binder for binder. Univs `ℓ`, `ℓi` (and `ℓ'` for
    // the eliminator) are pushed in that order. Every `IWf` branch opens with
    // the signature's six globals `g, I, S, n, o, c` ([`iwf_sig_globals`]),
    // and `x_I … x_c` are its recursive results, each at the motive over the
    // context its piece lives in.
    let iwf_sig_locals = |coded: bool, univs: u32, tg: u32, v: &IWfView, gt: &LocalCtx| {
        let sig = &v.sig;
        let (l, li) = (&sig.level, &sig.idx_level);
        let k = tg - 6;
        let (x_i, x_s) = if coded {
            let piece = |var: u32, level: &Level, at: u32| {
                inst_tm_motive(
                    m_tm,
                    (univs, tg, at),
                    Level::succ(level.clone()),
                    v.g.clone(),
                    Type::Ty(level.clone()),
                    Term::BoxTm(Rc::new(gtm(var, &v.g))),
                    gt,
                )
            };
            ((piece(k + 4, li, 0), l2.shift(univs, 0)), (piece(k + 3, l, 1), l2.shift(univs, 0)))
        } else {
            let piece = |ty: &Rc<Type>, level: &Level, at: u32| {
                inst_ty_motive(m_ty, (univs, tg, at), level.clone(), v.g.clone(), Term::BoxTy(Rc::clone(ty)), gt)
            };
            ((piece(&sig.idx, li, 0), l1.shift(univs, 0)), (piece(&sig.shape, l, 1), l1.shift(univs, 0)))
        };
        let x_n = inst_tm_motive(
            m_tm,
            (univs, tg, 2),
            Level::Zero,
            v.gx.clone(),
            Type::Nat,
            Term::BoxTm(Rc::clone(&sig.arity)),
            gt,
        );
        let x_o = inst_tm_motive(
            m_tm,
            (univs, tg, 3),
            li.clone(),
            v.gx.clone(),
            sig.idx.shift_local(1),
            Term::BoxTm(Rc::clone(&sig.out)),
            gt,
        );
        let x_c = inst_tm_motive(
            m_tm,
            (univs, tg, 4),
            li.clone(),
            v.gxi.clone(),
            sig.idx.shift_local(2),
            Term::BoxTm(Rc::clone(&sig.child)),
            gt,
        );
        vec![
            (Rc::new(x_i.0), x_i.1),
            (Rc::new(x_s.0), x_s.1),
            (Rc::new(x_n), l2.shift(univs, 0)),
            (Rc::new(x_o), l2.shift(univs, 0)),
            (Rc::new(x_c), l2.shift(univs, 0)),
        ]
    };

    // (ℓ, g, u_n : Trm_c(g ⊢ Nat @ 0), U_F : Typ_c((g, i : Fin u_n^id @ 0), ℓ),
    //  x_n, x_F. t_DVec) : M_Typ[ℓ/ℓ, g/g, box DVec^ℓ(u_n^id; i. U_F^id)/x_T]
    // (55), and (ℓ, g, u_n, u_f : Trm_c((g, i) ⊢ Ty ℓ @ 1+ℓ), x_n, x_f.
    // t'_DVec) : M_Trm[1+ℓ/ℓ, g/g, Ty ℓ/U_T, box DVec^ℓ(u_n^id; i. u_f^id)/x_t]
    // (56). The length is a term of g, so x_n is at the *term* motive.
    let (ty_dvec, tm_dvec) = {
        let make = |coded: bool| {
            let l = lvar(0);
            let gt = gt(1, 3);
            let fam_binding = |ctx: LocalCtx| {
                if coded {
                    GlobalBinding::Tm {
                        ctx,
                        layer: Layer::Code,
                        ty: Rc::new(Type::Ty(l.clone())),
                        level: Level::succ(l.clone()),
                        body: None,
                    }
                } else {
                    GlobalBinding::Ty { ctx, layer: Layer::Code, level: l.clone() }
                }
            };
            // U_F's prefix (g, u_n): g = 1, u_n = 0.
            let g1 = g_ctx(1);
            let globals = vec![
                GlobalBinding::Ctx,
                GlobalBinding::Tm {
                    ctx: g_ctx(0),
                    layer: Layer::Code,
                    ty: Rc::new(Type::Nat),
                    level: Level::Zero,
                    body: None,
                },
                fam_binding(ext_ctx(&g1, Type::Fin { len: Rc::new(gtm(0, &g1)) }, Level::Zero)),
            ];
            // Telescope view: g = 2, u_n = 1, U_F = 0.
            let g2 = g_ctx(2);
            let len = Rc::new(gtm(1, &g2));
            let gi = ext_ctx(&g2, Type::Fin { len: Rc::clone(&len) }, Level::Zero);
            let x_n = inst_tm_motive(m_tm, (1, 3, 0), Level::Zero, g2.clone(), Type::Nat, Term::BoxTm(Rc::clone(&len)), &gt);
            let (x_f, ty) = if coded {
                let fam = Rc::new(gtm(0, &gi));
                let x_f = inst_tm_motive(
                    m_tm,
                    (1, 3, 1),
                    Level::succ(l.clone()),
                    gi.clone(),
                    Type::Ty(l.clone()),
                    Term::BoxTm(Rc::clone(&fam)),
                    &gt,
                );
                let code = Term::TmDVec { level: l.clone(), len: Rc::clone(&len), fam };
                let ty = inst_tm_motive(
                    m_tm,
                    (1, 3, 2),
                    Level::succ(l.clone()),
                    g2.clone(),
                    Type::Ty(l.clone()),
                    Term::BoxTm(Rc::new(code)),
                    &gt,
                );
                ((x_f, l2.shift(1, 0)), ty)
            } else {
                let fam = Rc::new(gty(0, &gi));
                let x_f = inst_ty_motive(m_ty, (1, 3, 1), l.clone(), gi.clone(), Term::BoxTy(Rc::clone(&fam)), &gt);
                let code = Type::DVec { level: l.clone(), len: Rc::clone(&len), fam };
                let ty = inst_ty_motive(m_ty, (1, 3, 2), l.clone(), g2.clone(), Term::BoxTy(Rc::new(code)), &gt);
                ((x_f, l1.shift(1, 0)), ty)
            };
            BranchSpec {
                tele: Tele {
                    univs: 1,
                    globals,
                    locals: vec![(Rc::new(x_n), l2.shift(1, 0)), (Rc::new(x_f.0), x_f.1)],
                },
                ty: Rc::new(ty),
                level: if coded { l2.shift(1, 0) } else { l1.shift(1, 0) },
            }
        };
        (make(false), make(true))
    };

    // (ℓ, ℓi, g, U_I, U_S, u_n, u_o, u_c, u_m : Trm_c(g ⊢ U_I^id @ ℓi),
    //  x_I, x_S, x_n, x_o, x_c, x_m. t_IWf)
    //   : M_Typ[ℓ⊔ℓi/ℓ, g/g, box IWf(U_I; U_S; u_n; u_o; u_c)(u_m^id)/x_T]
    // (57), and its coded twin t'_IWf (58) at M_Trm[1+(ℓ⊔ℓi)/ℓ, g/g,
    // Ty(ℓ⊔ℓi)/U_T, box TmIWf(…)/x_t].
    let (ty_iwf, tm_iwf) = {
        let make = |coded: bool| {
            let (l, li) = (lvar(1), lvar(0));
            let gt = gt(2, 7);
            // u_m's prefix (g, I, S, n, o, c): c = 0.
            let pre = iwf_view(coded, 0, &l, &li);
            let mut globals = iwf_sig_globals(coded, &l, &li);
            globals.push(GlobalBinding::Tm {
                ctx: pre.g.clone(),
                layer: Layer::Code,
                ty: Rc::clone(&pre.sig.idx),
                level: li.clone(),
                body: None,
            });
            // Telescope view: g = 6, I = 5, S = 4, n = 3, o = 2, c = 1, m = 0.
            let v = iwf_view(coded, 1, &l, &li);
            let m = Rc::new(gtm(0, &v.g));
            let mut locals = iwf_sig_locals(coded, 2, 7, &v, &gt);
            locals.push((
                Rc::new(inst_tm_motive(
                    m_tm,
                    (2, 7, 5),
                    li.clone(),
                    v.g.clone(),
                    (*v.sig.idx).clone(),
                    Term::BoxTm(Rc::clone(&m)),
                    &gt,
                )),
                l2.shift(2, 0),
            ));
            let family = v.sig.family_level();
            let ty = if coded {
                let code = Term::TmIWf {
                    level: l.clone(),
                    idx_level: li.clone(),
                    idx: Rc::new(gtm(5, &v.g)),
                    shape: Rc::new(gtm(4, &v.g)),
                    arity: Rc::clone(&v.sig.arity),
                    out: Rc::clone(&v.sig.out),
                    child: Rc::clone(&v.sig.child),
                    index: Rc::clone(&m),
                };
                inst_tm_motive(
                    m_tm,
                    (2, 7, 6),
                    Level::succ(family.clone()),
                    v.g.clone(),
                    Type::Ty(family),
                    Term::BoxTm(Rc::new(code)),
                    &gt,
                )
            } else {
                inst_ty_motive(m_ty, (2, 7, 6), family, v.g.clone(), Term::BoxTy(Rc::new(v.sig.at(m))), &gt)
            };
            BranchSpec {
                tele: Tele { univs: 2, globals, locals },
                ty: Rc::new(ty),
                level: if coded { l2.shift(2, 0) } else { l1.shift(2, 0) },
            }
        };
        (make(false), make(true))
    };

    // (ℓ, ℓi, g, U_I, U_S, u_n, u_o, u_c, u_a : Trm_c(g ⊢ U_S^id @ ℓ),
    //  u_cs : Trm_c(g ⊢ DVec^{ℓ⊔ℓi}(u_n[u_a]; k. IWf(…)(u_c[u_a, k])) @ ℓ⊔ℓi),
    //  x_I, x_S, x_n, x_o, x_c, x_a, x_cs. t_supi)
    //   : M_Trm[ℓ⊔ℓi/ℓ, g/g, IWf(…)(u_o[u_a])/U_T, box sup_i(…; u_a; u_cs)/x_t]
    // (59). The children's type is `iwf_children_ty`, as in the typing rule.
    let tm_sup_i = {
        let (l, li) = (lvar(1), lvar(0));
        let gt = gt(2, 8);
        let mut globals = iwf_sig_globals(false, &l, &li);
        // u_a, prefix (…, c): c = 0.
        let v0 = iwf_view(false, 0, &l, &li);
        globals.push(GlobalBinding::Tm {
            ctx: v0.g.clone(),
            layer: Layer::Code,
            ty: Rc::clone(&v0.sig.shape),
            level: l.clone(),
            body: None,
        });
        // u_cs, prefix (…, c, a): c = 1, a = 0.
        let v1 = iwf_view(false, 1, &l, &li);
        globals.push(GlobalBinding::Tm {
            ctx: v1.g.clone(),
            layer: Layer::Code,
            ty: Rc::new(iwf_children_ty(&v1.sig, &gtm(0, &v1.g))),
            level: v1.sig.family_level(),
            body: None,
        });
        // Telescope view: g = 7, I = 6, S = 5, n = 4, o = 3, c = 2, a = 1,
        // cs = 0.
        let v = iwf_view(false, 2, &l, &li);
        let a = Rc::new(gtm(1, &v.g));
        let cs = Rc::new(gtm(0, &v.g));
        let family = v.sig.family_level();
        let mut locals = iwf_sig_locals(false, 2, 8, &v, &gt);
        locals.push((
            Rc::new(inst_tm_motive(
                m_tm,
                (2, 8, 5),
                l.clone(),
                v.g.clone(),
                (*v.sig.shape).clone(),
                Term::BoxTm(Rc::clone(&a)),
                &gt,
            )),
            l2.shift(2, 0),
        ));
        locals.push((
            Rc::new(inst_tm_motive(
                m_tm,
                (2, 8, 6),
                family.clone(),
                v.g.clone(),
                iwf_children_ty(&v.sig, &a),
                Term::BoxTm(Rc::clone(&cs)),
                &gt,
            )),
            l2.shift(2, 0),
        ));
        let out_at = v.sig.at(Rc::new(v.sig.out.inst_top(0, &a)));
        let code = v.sig.supi(a, cs);
        BranchSpec {
            tele: Tele { univs: 2, globals, locals },
            ty: Rc::new(inst_tm_motive(
                m_tm,
                (2, 8, 7),
                family,
                v.g.clone(),
                out_at,
                Term::BoxTm(Rc::new(code)),
                &gt,
            )),
            level: l2.shift(2, 0),
        }
    };

    // (ℓ, ℓi, ℓ', g, U_I, U_S, u_n, u_o, u_c,
    //  U_M : Typ_c((g, j : U_I^id, z : IWf(…)(j)), ℓ'),
    //  u_s : Trm_c((g, a, cs, ih) ⊢ U_M^{id, u_o[a]/j, sup_i(a; cs)/z} @ ℓ'),
    //  u_m : Trm_c(g ⊢ U_I^id @ ℓi), u_t : Trm_c(g ⊢ IWf(…)(u_m^id) @ ℓ⊔ℓi),
    //  x_I, x_S, x_n, x_o, x_c, x_M, x_s, x_m, x_t. t_elimIWf)
    //   : M_Trm[ℓ'/ℓ, g/g, U_M^{id, u_m/j, u_t/z}/U_T,
    //           box elim_IWf(…; j z. U_M^id; a cs ih. u_s^id; u_m; u_t)/x_t]
    // (60). The step telescope is `iwf_step_telescope`, exactly as in the
    // typing rule; x_M is at the *type* motive.
    let tm_elim_iwf = {
        let (l, li, lm) = (lvar(2), lvar(1), lvar(0));
        let gt = gt(3, 10);
        // `(g, j : I, z : IWf(…)(j))` and the step's `(g, a, cs, ih)` with
        // its type, for a view whose motive is the global `motive_at`.
        let scopes = |v: &IWfView, motive_at: u32| {
            let gj = ext_ctx(&v.g, (*v.sig.idx).clone(), v.sig.idx_level.clone());
            let gjz = ext_ctx(&gj, iwf_motive_scrut_ty(&v.sig), v.sig.family_level());
            let motive = gty(motive_at, &gjz);
            let (cs_ty, ih_ty, step_ty) = iwf_step_telescope(&v.sig, &lm, &motive);
            let ga = ext_ctx(&v.g, (*v.sig.shape).clone(), v.sig.level.clone());
            let gacs = ext_ctx(&ga, cs_ty, v.sig.family_level());
            let gacsi = ext_ctx(&gacs, ih_ty, lm.clone());
            (gjz, motive, gacsi, step_ty)
        };
        let mut globals = iwf_sig_globals(false, &l, &li);
        // U_M, prefix (…, c): c = 0.
        let v0 = iwf_view(false, 0, &l, &li);
        let (gjz0, _, _, _) = scopes(&v0, 0);
        globals.push(GlobalBinding::Ty { ctx: gjz0, layer: Layer::Code, level: lm.clone() });
        // u_s, prefix (…, c, M): c = 1, M = 0.
        let v1 = iwf_view(false, 1, &l, &li);
        let (_, _, gacsi1, step_ty1) = scopes(&v1, 0);
        globals.push(GlobalBinding::Tm {
            ctx: gacsi1,
            layer: Layer::Code,
            ty: Rc::new(step_ty1),
            level: lm.clone(),
            body: None,
        });
        // u_m, prefix (…, c, M, s): c = 2.
        let v2 = iwf_view(false, 2, &l, &li);
        globals.push(GlobalBinding::Tm {
            ctx: v2.g.clone(),
            layer: Layer::Code,
            ty: Rc::clone(&v2.sig.idx),
            level: li.clone(),
            body: None,
        });
        // u_t, prefix (…, c, M, s, m): c = 3, m = 0.
        let v3 = iwf_view(false, 3, &l, &li);
        globals.push(GlobalBinding::Tm {
            ctx: v3.g.clone(),
            layer: Layer::Code,
            ty: Rc::new(v3.sig.at(Rc::new(gtm(0, &v3.g)))),
            level: v3.sig.family_level(),
            body: None,
        });
        // Telescope view: g = 9, I = 8, S = 7, n = 6, o = 5, c = 4, M = 3,
        // s = 2, m = 1, t = 0.
        let v = iwf_view(false, 4, &l, &li);
        let (gjz, motive, gacsi, step_ty) = scopes(&v, 3);
        let motive = Rc::new(motive);
        let step = Rc::new(gtm(2, &gacsi));
        let m = Rc::new(gtm(1, &v.g));
        let t = Rc::new(gtm(0, &v.g));
        let family = v.sig.family_level();
        let mut locals = iwf_sig_locals(false, 3, 10, &v, &gt);
        locals.push((
            Rc::new(inst_ty_motive(m_ty, (3, 10, 5), lm.clone(), gjz, Term::BoxTy(Rc::clone(&motive)), &gt)),
            l1.shift(3, 0),
        ));
        locals.push((
            Rc::new(inst_tm_motive(m_tm, (3, 10, 6), lm.clone(), gacsi, step_ty, Term::BoxTm(Rc::clone(&step)), &gt)),
            l2.shift(3, 0),
        ));
        locals.push((
            Rc::new(inst_tm_motive(
                m_tm,
                (3, 10, 7),
                li.clone(),
                v.g.clone(),
                (*v.sig.idx).clone(),
                Term::BoxTm(Rc::clone(&m)),
                &gt,
            )),
            l2.shift(3, 0),
        ));
        locals.push((
            Rc::new(inst_tm_motive(
                m_tm,
                (3, 10, 8),
                family,
                v.g.clone(),
                v.sig.at(Rc::clone(&m)),
                Term::BoxTm(Rc::clone(&t)),
                &gt,
            )),
            l2.shift(3, 0),
        ));
        let at_scrut = inst_motive2(&motive, 0, &m, &t);
        let code = Term::ElimIWf {
            sig: Rc::clone(&v.sig),
            motive_level: lm.clone(),
            motive,
            step,
            index: m,
            scrut: t,
        };
        BranchSpec {
            tele: Tele { univs: 3, globals, locals },
            ty: Rc::new(inst_tm_motive(
                m_tm,
                (3, 10, 9),
                lm.clone(),
                v.g.clone(),
                at_scrut,
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
        tm_sum, tm_inl, tm_inr, tm_case, ty_w, tm_w, tm_sup, tm_elim_w, ty_vec, tm_vec,
        ty_fin, tm_fin, ty_wf, tm_wf, tm_supf, tm_elim_wf, ty_seq, tm_seq, ty_sempty,
        tm_sempty, tm_srefl, tm_elim_sempty,
        ty_squash, tm_squash, tm_squash_in, tm_elim_squash,
        ty_m, tm_m, tm_corec, tm_out,
        ty_dvec, tm_dvec, ty_iwf, tm_iwf, tm_sup_i, tm_elim_iwf,
    ]
}

// ---------------------------------------------------------------------------
// Well-formedness of the telescopes themselves
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::term::Motives;
    use crate::typing::{check_global_ctx, check_type};

    /// Enough for the whole 65-branch walk: every judgment here is a small
    /// contextual type, and the walk is linear in the tables.
    const FUEL: u64 = 1 << 16;

    /// The identity motives — `M_Typ := □(g ⊢ Ty ℓ)`, `M_Trm := □(g ⊢ U_T^id
    /// @ ℓ)` — the sharpest *well-formedness* observer of the two live motive
    /// families (see the module test's doc comment).
    fn identity_motives() -> Motives {
        Motives {
            ty_motive: Rc::new(Type::CodeTy { ctx: g_ctx(0), level: lvar(0) }),
            tm_motive: Rc::new(Type::CodeTm {
                ctx: g_ctx(1),
                ty: Rc::new(gty(0, &g_ctx(1))),
                level: lvar(0),
            }),
        }
    }

    /// Check one telescope: its global bindings as a Ψ, then each local entry
    /// as a type at its declared level under the prefix that precedes it.
    /// `label` names the site; failures report the label and the entry index
    /// only — never a term (the kernel's `Debug` is bounded, but a
    /// 65-telescope walk is no place to exercise it).
    fn check_tele(label: &str, tele: &Tele) -> (GlobalCtx, LocalCtx) {
        // The ambient scope is `(L; Ψ; Γ) = (0; ·; ·)` at layer `m`: `rec_ga`
        // runs under `meta_layer`, and `push_spec` keeps the layer, so this
        // is the scope the checker really uses for these entries. An empty
        // ambient Ψ/Γ loses nothing — every telescope is closed except for
        // its own binders, and the motive instantiations weaken the ambient
        // Γ in uniformly.
        let psi = {
            let mut p = shift_univ_psi(&GlobalCtx::new(vec![]), tele.univs);
            p.extend(tele.globals.iter().cloned());
            p
        };
        assert!(
            check_global_ctx(&psi, tele.univs, FUEL).is_ok(),
            "{label}: telescope global bindings are not a well-formed Ψ",
        );
        let mut gamma = LocalCtx::nil();
        for (i, (ty, level)) in tele.locals.iter().enumerate() {
            let r = check_type(&psi, tele.univs, Layer::Meta, &gamma, ty, level, FUEL);
            assert!(
                r.is_ok(),
                "{label}: telescope local entry #{i} is not a well-formed type \
                 at its declared level ({:?})",
                r.unwrap_err(),
            );
            gamma = gamma.extended(Rc::clone(ty), level.clone());
        }
        (psi, gamma)
    }

    /// Every local entry of every branch telescope must be a *type*.
    ///
    /// `rec_ga` checks branch bodies against their instantiated motive types
    /// but never asks whether the telescope's own entries — the recursive
    /// calls `x_M`, `x_t`, … — are well-formed. An ill-formed entry is dead
    /// on arrival: nothing well-formed can be checked against it, so no
    /// branch can use its own recursive call and nothing complains. That is
    /// exactly how a mis-levelled `□(g ⊢ Empty^{ℓ'} @ ℓ)` survived two
    /// level-indexing rounds ([[recursor-elim-call-level-mismatch]]).
    ///
    /// Under the **identity** motives the term-motive entries carry both
    /// slots that can disagree: `M_Trm[l/ℓ, …, U/U_T, …]` instantiates to
    /// `□(g ⊢ U @ l)`, whose well-formedness *is* the judgment `g ⊢ U @ l` —
    /// so a recursive call declared at the motive's level when its scrutinee
    /// lives at another is caught here as "not a type at all". A motive that
    /// ignores `U_T` (e.g. `M_Trm := □(g ⊢ Ty ℓ)`) would make such an entry
    /// well-formed and hence *unobservable* by this check; the identity
    /// motives are therefore the sharper observer for well-formedness, and
    /// the weaker one for use-site behaviour. Type-motive entries
    /// (`□(g ⊢ Ty l)`) constrain only `g` and the level's scope, not the
    /// level's *value* — see the report note on the `Ty ℓ`-motive bundle.
    #[test]
    fn every_branch_telescope_entry_is_a_well_formed_type() {
        let motives = identity_motives();
        let (l1, l2) = (Level::Zero, Level::Zero);
        let gamma = LocalCtx::nil();

        for (spec, label) in motive_specs(&l1, &l2).iter().zip(["M_Typ", "M_Trm"]) {
            check_tele(label, &spec.tele);
        }

        let specs = branch_specs(&motives, &l1, &l2, &gamma);
        assert_eq!(specs.len(), BRANCH_NAMES.len());
        for (spec, name) in specs.iter().zip(BRANCH_NAMES) {
            let (psi, gamma) = check_tele(name, &spec.tele);
            // The branch's own expected type, while we are here: an
            // ill-formed one is unsatisfiable in the same silent way.
            let r = check_type(
                &psi,
                spec.tele.univs,
                Layer::Meta,
                &gamma,
                &spec.ty,
                &spec.level,
                FUEL,
            );
            assert!(
                r.is_ok(),
                "{name}: the branch's expected type is not well formed at its \
                 declared level ({:?})",
                r.unwrap_err(),
            );
        }
    }

    /// The `(ctx, level)` slots of the *type-motive* recursive calls
    /// (`x_S`, `x_T`, `x_M`, …), which no well-formedness check can see.
    ///
    /// `M_Typ[l/ℓ, Δ/g, …]` instantiates to `□(Δ ⊢ Ty l)`, and that is a type
    /// for *any* in-scope `l` and any well-formed `Δ` — so
    /// [`every_branch_telescope_entry_is_a_well_formed_type`] checks the
    /// level's **scope** and never its **value**
    /// ([[branch-telescope-type-motive-level-slots]]). The slots are pinned
    /// here instead, by the one thing in the same table that already knows
    /// the answer.
    ///
    /// **The invariant.** A type-motive recursive call is the call on a
    /// sub-*code* of the code being eliminated, and every sub-code a branch
    /// destructures is bound by that branch's telescope as a **layer-c**
    /// `Typ_c(Δ_k, l_k)` global. `reduce.rs` hands the *same* payload to
    /// both slots — `fire` passes `GlobalEntry::Ty(dom)` for `U_S` and
    /// `rec.elim_ty(dom_level, Δ, dom)` for `x_S` — and `typing.rs` gives
    /// `elim^Typ(l, Δ, box X)` the type `M_Typ[l/ℓ, Δ/g, box X/x_T]`. So the
    /// call's `(Δ, l)` *must* be the binding's `(Δ_k, l_k)`, and the two
    /// independently hand-written halves of each branch spec — its
    /// `globals:` list and its `inst_ty_motive` arguments — must agree.
    ///
    /// The correspondence is the identity on order and, in all 65 branches,
    /// a **bijection**: `n` layer-c `Ty` globals ⟺ `n` type-motive calls, in
    /// the same order. Layer-**p** `Ty` globals are the exception that
    /// explains the rule, and it is the paper's own
    /// (`docs/kernel/delam-extensions.md` §16.5): a `Typ_c` binding is a sub-code
    /// and carries a recursive call, a `Typ_p` binding is an *external
    /// index* and carries none. `t_x`'s and `t_λ`'s `U_T` are the only two,
    /// because a `λ` does not store its codomain. The count assertion below
    /// fails if any binding grows or loses a call. The remaining locals are
    /// term-motive calls, whose slots formation already pins (see the
    /// sibling test).
    ///
    /// 67 slots are covered (ten of them `M`'s, eight `DVec`'s and
    /// `IWf`'s); the enumeration is
    /// `branch_specs` itself, read off by this walk rather than transcribed.
    #[test]
    fn every_type_motive_recursive_call_matches_its_code_layer_type_binding() {
        let motives = identity_motives();
        let (l1, l2) = (Level::Zero, Level::Zero);
        let gamma = LocalCtx::nil();
        let specs = branch_specs(&motives, &l1, &l2, &gamma);

        let mut covered = 0usize;
        for (spec, name) in specs.iter().zip(BRANCH_NAMES) {
            let n = spec.tele.globals.len() as u32;
            // The layer-c `Typ_c(Δ_k, l_k)` bindings, brought from the
            // Ψ-prefix they are scoped in to the whole telescope's scope.
            let bound_codes: Vec<Type> = spec
                .tele
                .globals
                .iter()
                .enumerate()
                .filter_map(|(j, b)| match b {
                    GlobalBinding::Ty { ctx, layer: Layer::Code, level } => Some(Type::CodeTy {
                        ctx: ctx.shift_global(n - j as u32),
                        level: level.clone(),
                    }),
                    _ => None,
                })
                .collect();
            // The type-motive calls: under the identity `M_Typ` an entry
            // instantiates to `□(Δ ⊢ Ty l)` exactly when it is one.
            let calls: Vec<(usize, &Rc<Type>)> = spec
                .tele
                .locals
                .iter()
                .enumerate()
                .filter(|(_, (ty, _))| matches!(&**ty, Type::CodeTy { .. }))
                .map(|(i, (ty, _))| (i, ty))
                .collect();

            assert_eq!(
                calls.len(),
                bound_codes.len(),
                "{name}: {} layer-c Typ_c globals but {} type-motive recursive \
                 calls — every sub-code the branch binds gets exactly one call",
                bound_codes.len(),
                calls.len(),
            );
            for (k, ((i, got), want)) in calls.iter().zip(&bound_codes).enumerate() {
                assert!(
                    ***got == *want,
                    "{name}: type-motive recursive call #{k} (telescope entry \
                     #{i}) does not match the layer-c Typ_c binding it \
                     recurses on — its context or universe-level slot is \
                     wrong (declared {:?}, binding says {:?})",
                    got,
                    want,
                );
                covered += 1;
            }
        }
        // A tripwire on the *scope* of this test: if a branch gains or loses
        // a type-motive recursive call, the enumeration in the issue and the
        // Coq `G_Typ` table both move with it.
        // 65 since `transp`'s two (its type and its motive) went with it
        // (docs/kernel/iwf-former-design.md §13 step 6).
        assert_eq!(covered, 65, "the number of type-motive recursive calls moved");
    }
}
