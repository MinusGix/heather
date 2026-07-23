//! The type checker: syntax-directed checking of the ch. 04 judgments
//! (docs/delam/04) over fully explicit core terms.
//!
//! | tex judgment            | here                                    |
//! |-------------------------|-----------------------------------------|
//! | `⊢_L Ψ`                 | [`check_global_ctx`]                    |
//! | `⊢_i Γ`                 | [`check_local_ctx`] / [`Tc::ctx_wf`]    |
//! | `⊢_i T @ l`             | [`check_type`] / [`Tc::ty_infer`]       |
//! | `⊢_i t : T @ l`         | [`check_term`] / [`Tc::tm_infer`]       |
//! | `⊢_i δ : Δ`             | [`check_local_subst`] / [`Tc::subst_ck`]|
//!
//! Algorithmic reading of the declarative rules:
//!
//! - **Bidirectional, inference-heavy.** Every form except `box` carries
//!   enough annotations to *infer* its type, so inference is primary and
//!   returns the **canonical** type and level of the rules' conclusions.
//!   Checking = infer + conversion at layer `typeof(i)` + level `≈` — the
//!   two conversion rules fire exactly there and nowhere else
//!   (non-cumulativity: levels compare by `≈`, never `≤`).
//! - **`box` is checking-only** (the tex rule pulls `Δ` and `l` out of thin
//!   air — they come from the expected type). Checking descends
//!   structurally through the four function intro forms (`λ`, `Λ ℓ⃗`,
//!   `Λ g`, `Λ U`) so `box` under them still checks. Consequence: a `box`
//!   in an un-annotated inference position (the body of an immediately
//!   β-reduced meta-function, e.g. `(Λ g. box Nat) @ Δ`) is rejected with
//!   [`TypeError::NotInferable`] even though it is declaratively typable —
//!   elaborators must name such code with `letbox` instead of redexing.
//! - **Elimination heads that lack annotations** (`t $ l⃗`, `t @ Δ`,
//!   `t @ T`) infer the head and weak-head-reduce its type to expose the
//!   function former, exactly as conversion's neutral inference does.
//! - **Layer discipline**: layer v admits only local/global variables (plus
//!   the built-in conversion); layer-m formers require layer m; global
//!   variables demand `i' ≤ i`; `ω` is accepted nowhere a programmer level
//!   is demanded ([`crate::level::Level::well_formed`]) and arises only as
//!   the inferred level of `ΠΠ`/`Λ ℓ⃗`.
//! - The recursor rules check the two motives and 28 branches against the
//!   `G_M G_Typ G_Trm` telescopes of [`crate::rec`] — the same tables
//!   conversion compares against.
//!
//! **Trust boundary / presuppositions.** Like conversion (see DESIGN.md),
//! each function presupposes the well-formedness of the ambient structures
//! it does not re-derive: `check_local_ctx` presupposes `⊢_L Ψ`;
//! `check_type`/`check_term`/`check_local_subst` additionally presuppose
//! `⊢_typeof(i) Γ`, and the expected type/target context they receive must
//! itself be well-formed. Rule premises that re-state the well-formedness
//! of something already presupposed well-formed (e.g. `⊢_typeof(i) Γ` on
//! every leaf rule, or the entry types of a substitution's target) are
//! deliberately not re-checked — re-deriving them at every node would be
//! exponential. A full check of a closed program is the composition:
//! `check_global_ctx`, then `check_local_ctx`, then `check_type` on the
//! goal type, then `check_term`.
//!
//! **Fuel.** The checker's own recursion is structural, so it terminates
//! without a budget; only conversion and weak-head normalization need one.
//! `fuel` is granted *per conversion call / per normalization* (not shared
//! globally): total work is bounded by `O(nodes · fuel)`. Exhaustion
//! surfaces as [`TypeError::OutOfFuel`], distinct from a mismatch. On
//! well-typed input it means the budget was too small; [`DEFAULT_FUEL`] is
//! a generous default.

use std::rc::Rc;

use crate::conv::{conv_local_ctx, conv_type, ConvError};
use crate::layer::Layer;
use crate::level::Level;
use crate::rec::{self, gtm, gty, inst_tm_motive, inst_ty_motive, shift_univ_psi};
use crate::reduce::whnf_type;
use crate::subst::{GlobalEntry, GlobalSubst};
use crate::term::{
    CtxBase, CtxEntry, GlobalBinding, GlobalCtx, GlobalVar, LocalCtx, LocalSubst, LocalVar,
    SubstTail, Term, Type,
};

/// A generous per-conversion fuel budget for callers without an opinion.
pub const DEFAULT_FUEL: u64 = 1 << 20;

/// Why type checking failed. Variants carry indices, not terms, so a
/// `Debug`-formatted error is always small.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TypeError {
    /// A conversion or weak-head normalization exhausted its fuel budget.
    OutOfFuel,
    /// The inferred type is not convertible to the expected type.
    NotConvertible,
    /// The inferred universe level is not `≈` the expected one.
    LevelMismatch,
    /// A level is not well-formed here: `ω`, or an out-of-scope `ℓ`.
    IllFormedLevel,
    /// A local variable exceeds `|Γ|`.
    UnboundLocalVar(u32),
    /// A global variable exceeds `|Ψ|`.
    UnboundGlobalVar(u32),
    /// The global binding at this index has the wrong kind (e.g. `U^δ`
    /// hitting a `g : Ctx` or `u : Trm` binding).
    WrongGlobalBinding(u32),
    /// A rule was used at a layer that does not admit it (layer-m former
    /// below m, non-variable term at layer v, binding layer `i' > i`, or a
    /// binding whose declared layer is outside its admissible set).
    LayerMismatch,
    /// A `box` in inference position: its contextual type is not inferable.
    NotInferable,
    /// The head of `$`/`@` does not have the corresponding function type,
    /// or a term was checked against a former it cannot inhabit.
    HeadMismatch,
    /// A universe-variable vector is empty or has the wrong length.
    UnivArityMismatch,
    /// A local substitution does not match its source Γ / target Δ shape
    /// (tail kind, tail length, base, or entry count).
    SubstMismatch,
}

type R<T = ()> = Result<T, TypeError>;

impl From<ConvError> for TypeError {
    fn from(e: ConvError) -> TypeError {
        match e {
            ConvError::OutOfFuel => TypeError::OutOfFuel,
            ConvError::NotConvertible => TypeError::NotConvertible,
        }
    }
}

// ---------------------------------------------------------------------------
// Public API
// ---------------------------------------------------------------------------

/// `⊢_L Ψ` — well-formedness of a global context under `univs` universe
/// variables.
pub fn check_global_ctx(psi: &GlobalCtx, univs: u32, fuel: u64) -> R {
    let tc = Tc { fuel };
    for (i, b) in psi.bindings.iter().enumerate() {
        let prefix = GlobalCtx { bindings: psi.bindings[..i].to_vec() };
        let env = Env {
            psi: prefix,
            gamma: LocalCtx { base: CtxBase::Nil, entries: vec![] },
            layer: Layer::Prog,
            univs,
        };
        match b {
            GlobalBinding::Ctx => {}
            GlobalBinding::Ty { ctx, layer, level } => {
                if !matches!(layer, Layer::Code | Layer::Prog) {
                    return Err(TypeError::LayerMismatch);
                }
                tc.level_wf(&env, level)?;
                tc.ctx_wf(&env, Layer::Prog, ctx)?;
            }
            GlobalBinding::Tm { ctx, layer, ty, level } => {
                if !matches!(layer, Layer::Var | Layer::Code) {
                    return Err(TypeError::LayerMismatch);
                }
                tc.level_wf(&env, level)?;
                tc.ctx_wf(&env, Layer::Prog, ctx)?;
                tc.ty_check(&env.in_ctx(ctx.clone(), Layer::Prog), ty, level)?;
            }
        }
    }
    Ok(())
}

/// `⊢_i Γ` — well-formedness of a local context. Presupposes `⊢_L Ψ`.
pub fn check_local_ctx(
    psi: &GlobalCtx,
    univs: u32,
    layer: Layer,
    gamma: &LocalCtx,
    fuel: u64,
) -> R {
    let env = Env {
        psi: psi.clone(),
        gamma: LocalCtx { base: CtxBase::Nil, entries: vec![] },
        layer,
        univs,
    };
    Tc { fuel }.ctx_wf(&env, layer, gamma)
}

/// `⊢_i T @ l` — the type `T` is well-formed at level `l`. Presupposes
/// `⊢_L Ψ` and `⊢_i Γ`.
pub fn check_type(
    psi: &GlobalCtx,
    univs: u32,
    layer: Layer,
    gamma: &LocalCtx,
    ty: &Type,
    level: &Level,
    fuel: u64,
) -> R {
    let env = Env { psi: psi.clone(), gamma: gamma.clone(), layer, univs };
    Tc { fuel }.ty_check(&env, ty, level)
}

/// `⊢_i T @ ?` — infer the canonical level of `T`. Presuppositions as
/// [`check_type`].
pub fn infer_type(
    psi: &GlobalCtx,
    univs: u32,
    layer: Layer,
    gamma: &LocalCtx,
    ty: &Type,
    fuel: u64,
) -> R<Level> {
    let env = Env { psi: psi.clone(), gamma: gamma.clone(), layer, univs };
    Tc { fuel }.ty_infer(&env, ty)
}

/// `⊢_i t : T @ l`. Presupposes `⊢_L Ψ`, `⊢_typeof(i) Γ`, and
/// `⊢_typeof(i) T @ l`.
#[allow(clippy::too_many_arguments)]
pub fn check_term(
    psi: &GlobalCtx,
    univs: u32,
    layer: Layer,
    gamma: &LocalCtx,
    t: &Term,
    ty: &Type,
    level: &Level,
    fuel: u64,
) -> R {
    let env = Env { psi: psi.clone(), gamma: gamma.clone(), layer, univs };
    Tc { fuel }.tm_check(&env, t, ty, level)
}

/// `⊢_i t : ? @ ?` — infer the canonical type and level of `t`.
/// Presuppositions as [`check_term`]. Fails with
/// [`TypeError::NotInferable`] on `box` (checking-only, see module docs).
pub fn infer_term(
    psi: &GlobalCtx,
    univs: u32,
    layer: Layer,
    gamma: &LocalCtx,
    t: &Term,
    fuel: u64,
) -> R<(Type, Level)> {
    let env = Env { psi: psi.clone(), gamma: gamma.clone(), layer, univs };
    Tc { fuel }.tm_infer(&env, t)
}

/// `⊢_i δ : Δ` — the local substitution `δ` maps `Δ` into `Γ`. Presupposes
/// `⊢_L Ψ`, `⊢_typeof(i) Γ`, and the well-formedness of `Δ` (with `Δ`
/// scoped in the same Ψ as `Γ` — shift it first when it comes from a
/// binding).
#[allow(clippy::too_many_arguments)]
pub fn check_local_subst(
    psi: &GlobalCtx,
    univs: u32,
    layer: Layer,
    gamma: &LocalCtx,
    delta: &LocalSubst,
    target: &LocalCtx,
    fuel: u64,
) -> R {
    let env = Env { psi: psi.clone(), gamma: gamma.clone(), layer, univs };
    Tc { fuel }.subst_ck(&env, delta, target)
}

// ---------------------------------------------------------------------------
// Environment
// ---------------------------------------------------------------------------

/// The ambient scope of a check: Ψ, Γ, the layer index, and `|L|` (unlike
/// conversion, typing must know the universe-context length to decide
/// `⊢_L l : Level`). Extending clones, as in conversion.
#[derive(Clone)]
struct Env {
    psi: GlobalCtx,
    gamma: LocalCtx,
    layer: Layer,
    univs: u32,
}

impl Env {
    /// Replace Γ (and the layer) — for premises stated in a different local
    /// context, e.g. `Ψ; Δ ⊢_p T @ l`.
    fn in_ctx(&self, gamma: LocalCtx, layer: Layer) -> Env {
        Env { gamma, layer, ..self.clone() }
    }

    /// `Γ, x : T @ l`.
    fn push_entry(&self, ty: Rc<Type>, level: Level) -> Env {
        let mut e = self.clone();
        e.gamma.entries.push(CtxEntry { ty, level });
        e
    }

    /// Push `tu` universe binders then the given global bindings; Ψ and Γ
    /// weaken accordingly (mirrors conversion's `push_tele`).
    fn push_tele(&self, tu: u32, globals: Vec<GlobalBinding>) -> Env {
        let tg = globals.len() as u32;
        let mut psi = shift_univ_psi(&self.psi, tu);
        psi.bindings.extend(globals);
        Env {
            psi,
            gamma: self.gamma.shift_univ(tu).shift_global(tg),
            layer: self.layer,
            univs: self.univs + tu,
        }
    }

    fn push_univs(&self, n: u32) -> Env {
        self.push_tele(n, vec![])
    }

    fn push_global(&self, b: GlobalBinding) -> Env {
        self.push_tele(0, vec![b])
    }

    fn push_spec(&self, tele: &rec::Tele) -> Env {
        let mut e = self.push_tele(tele.univs, tele.globals.clone());
        for (ty, level) in &tele.locals {
            e = e.push_entry(Rc::clone(ty), level.clone());
        }
        e
    }
}

/// Ψ-lookup: 0 is innermost; the result is scoped over its *prefix* of Ψ —
/// callers shift by `v + 1`.
fn lookup(psi: &GlobalCtx, v: GlobalVar) -> Option<&GlobalBinding> {
    psi.bindings.len().checked_sub(1 + v.0 as usize).and_then(|i| psi.bindings.get(i))
}

// ---------------------------------------------------------------------------
// The checker
// ---------------------------------------------------------------------------

struct Tc {
    /// Per-conversion / per-normalization budget (see module docs).
    fuel: u64,
}

impl Tc {
    // -- premise helpers ----------------------------------------------------

    /// `⊢_L l : Level` (rejects `ω` and out-of-scope variables).
    fn level_wf(&self, env: &Env, l: &Level) -> R {
        if l.well_formed(env.univs) { Ok(()) } else { Err(TypeError::IllFormedLevel) }
    }

    /// `⊢_L l ≈ l' : Level` (as a premise; `ω ≈ ω` only).
    fn lev_eq(&self, a: &Level, b: &Level) -> R {
        if a.equiv(b) { Ok(()) } else { Err(TypeError::LevelMismatch) }
    }

    /// The conversion rule: `⊢_typeof(i) T ≈ T' @ l`.
    fn conv_ty(&self, env: &Env, expected: &Type, inferred: &Type, l: &Level) -> R {
        let at = env.layer.type_layer();
        conv_type(&env.psi, &env.gamma, at, expected, inferred, l, self.fuel)?;
        Ok(())
    }

    /// `T ⇝* W` under the checker's budget.
    fn whnf(&self, env: &Env, t: &Type) -> R<Type> {
        whnf_type(t, &env.gamma, self.fuel).map_err(|_| TypeError::OutOfFuel)
    }

    /// Reject everything at layer v except the forms listed in ch. 04's
    /// "Note on Layer v Rules".
    fn not_var_layer(&self, env: &Env) -> R {
        if env.layer == Layer::Var { Err(TypeError::LayerMismatch) } else { Ok(()) }
    }

    fn meta_layer(&self, env: &Env) -> R {
        if env.layer == Layer::Meta { Ok(()) } else { Err(TypeError::LayerMismatch) }
    }

    // -- local contexts -----------------------------------------------------

    /// `⊢_i Γ` (in `env.psi`; `env.gamma` is irrelevant).
    fn ctx_wf(&self, env: &Env, layer: Layer, gamma: &LocalCtx) -> R {
        if let CtxBase::Var(g) = gamma.base {
            match lookup(&env.psi, g) {
                Some(GlobalBinding::Ctx) => {}
                Some(_) => return Err(TypeError::WrongGlobalBinding(g.0)),
                None => return Err(TypeError::UnboundGlobalVar(g.0)),
            }
        }
        for k in 0..gamma.entries.len() {
            let prefix = LocalCtx { base: gamma.base, entries: gamma.entries[..k].to_vec() };
            let e = env.in_ctx(prefix, layer);
            let entry = &gamma.entries[k];
            self.level_wf(&e, &entry.level)?;
            self.ty_check(&e, &entry.ty, &entry.level)?;
        }
        Ok(())
    }

    // -- local substitutions ------------------------------------------------

    /// `⊢_i δ : Δ`, structure against Γ (source) and Δ (target). The target
    /// is presupposed well-formed, so its entry types are not re-checked —
    /// only the substituted terms are.
    fn subst_ck(&self, env: &Env, delta: &LocalSubst, target: &LocalCtx) -> R {
        // The tail covers Δ's base and must record Γ's exact shape.
        let src_len = env.gamma.entries.len() as u32;
        match (target.base, delta.tail) {
            (CtxBase::Nil, SubstTail::Empty { len, base }) => {
                if len != src_len || base != env.gamma.base {
                    return Err(TypeError::SubstMismatch);
                }
            }
            (CtxBase::Var(g), SubstTail::Wk { len, ctx_var }) => {
                if len != src_len || ctx_var != g || env.gamma.base != CtxBase::Var(g) {
                    return Err(TypeError::SubstMismatch);
                }
            }
            _ => return Err(TypeError::SubstMismatch),
        }
        if delta.terms.len() != target.entries.len() {
            return Err(TypeError::SubstMismatch);
        }
        // Step cases: ⊢_i t_k : T_k[δ_{<k}] @ l_k.
        for (k, entry) in target.entries.iter().enumerate() {
            let prefix = LocalSubst { tail: delta.tail, terms: delta.terms[..k].to_vec() };
            let ty = entry.ty.apply_local(&prefix);
            self.tm_check(env, &delta.terms[k], &ty, &entry.level)?;
        }
        Ok(())
    }

    // -- types --------------------------------------------------------------

    /// `⊢_i T @ l` for a given `l`: infer the canonical level and compare
    /// (the level-conversion rule).
    fn ty_check(&self, env: &Env, t: &Type, l: &Level) -> R {
        let inferred = self.ty_infer(env, t)?;
        self.lev_eq(l, &inferred)
    }

    /// `⊢_i T @ ?` — infer the canonical level of `T`. No type formation
    /// rule is stated at layer v.
    fn ty_infer(&self, env: &Env, t: &Type) -> R<Level> {
        self.not_var_layer(env)?;
        match t {
            Type::Nat => Ok(Level::Zero),
            Type::Pi { dom_level, cod_level, dom, cod } => {
                self.level_wf(env, dom_level)?;
                self.level_wf(env, cod_level)?;
                self.ty_check(env, dom, dom_level)?;
                let e = env.push_entry(Rc::clone(dom), dom_level.clone());
                self.ty_check(&e, cod, cod_level)?;
                Ok(Level::max(dom_level.clone(), cod_level.clone()))
            }
            Type::Ty(l) => {
                self.level_wf(env, l)?;
                Ok(Level::succ(l.clone()))
            }
            Type::UPi { num_vars, level, body } => {
                self.meta_layer(env)?;
                if *num_vars == 0 {
                    return Err(TypeError::UnivArityMismatch);
                }
                let e = env.push_univs(*num_vars);
                self.level_wf(&e, level)?;
                self.ty_check(&e, body, level)?;
                Ok(Level::Omega)
            }
            Type::El { level, tm } => {
                self.level_wf(env, level)?;
                self.tm_check(env, tm, &Type::Ty(level.clone()), &Level::succ(level.clone()))?;
                Ok(level.clone())
            }
            // Id-formation (extension beyond ch. 04; kernel-v1-extensions):
            // ⊢_i Id^l (S; t; u) @ l ⟸ ⊢_i S @ l, ⊢_i t : S @ l, ⊢_i u : S @ l
            Type::Id { level, ty, lhs, rhs } => {
                self.level_wf(env, level)?;
                self.ty_check(env, ty, level)?;
                self.tm_check(env, lhs, ty, level)?;
                self.tm_check(env, rhs, ty, level)?;
                Ok(level.clone())
            }
            // Σ-formation (extension beyond ch. 04; kernel-v1-extensions):
            // ⊢_i Σ^{l,l'}(x:S).T @ l⊔l' ⟸ ⊢_i S @ l, (Γ, x:S) ⊢_i T @ l'
            Type::Sigma { fst_level, snd_level, fst, snd } => {
                self.level_wf(env, fst_level)?;
                self.level_wf(env, snd_level)?;
                self.ty_check(env, fst, fst_level)?;
                let e = env.push_entry(Rc::clone(fst), fst_level.clone());
                self.ty_check(&e, snd, snd_level)?;
                Ok(Level::max(fst_level.clone(), snd_level.clone()))
            }
            // Unit/Empty-formation (extension beyond ch. 04): ⊢_i Unit @ 0,
            // ⊢_i Empty @ 0.
            Type::Unit | Type::Empty => Ok(Level::Zero),
            Type::GlobalTy { var, subst } => {
                let Some(binding) = lookup(&env.psi, *var) else {
                    return Err(TypeError::UnboundGlobalVar(var.0));
                };
                let GlobalBinding::Ty { ctx, layer, level } = binding else {
                    return Err(TypeError::WrongGlobalBinding(var.0));
                };
                // i' ∈ {c, p} is the binding invariant; i' ≤ i:
                if *layer > env.layer {
                    return Err(TypeError::LayerMismatch);
                }
                let level = level.clone();
                let ctx = ctx.shift_global(var.0 + 1);
                self.subst_ck(env, subst, &ctx)?;
                Ok(level)
            }
            Type::CtxPi { level, body } => {
                self.meta_layer(env)?;
                self.level_wf(env, level)?;
                let e = env.push_global(GlobalBinding::Ctx);
                self.ty_check(&e, body, level)?;
                Ok(level.clone())
            }
            Type::TyPi { ctx, arg_level, body_level, body } => {
                self.meta_layer(env)?;
                self.level_wf(env, arg_level)?;
                self.level_wf(env, body_level)?;
                self.ctx_wf(env, Layer::Prog, ctx)?;
                let e = env.push_global(GlobalBinding::Ty {
                    ctx: ctx.clone(),
                    layer: Layer::Prog,
                    level: arg_level.clone(),
                });
                self.ty_check(&e, body, body_level)?;
                Ok(body_level.clone())
            }
            Type::CodeTy { ctx, level } => {
                self.meta_layer(env)?;
                self.level_wf(env, level)?;
                self.ctx_wf(env, Layer::Prog, ctx)?;
                Ok(Level::Zero)
            }
            Type::CodeTm { ctx, ty, level } => {
                self.meta_layer(env)?;
                self.level_wf(env, level)?;
                self.ctx_wf(env, Layer::Prog, ctx)?;
                self.ty_check(&env.in_ctx(ctx.clone(), Layer::Prog), ty, level)?;
                Ok(Level::Zero)
            }
        }
    }

    // -- terms --------------------------------------------------------------

    /// `⊢_i t : T @ l` for a given type and level: structural on `box` and
    /// the function intro forms (so checking-only `box` bodies work), else
    /// infer + conversion at `typeof(i)`.
    fn tm_check(&self, env: &Env, t: &Term, ty: &Type, l: &Level) -> R {
        match t {
            // box T : □(Δ ⊢ Ty l) @ 0 ⟸ Ψ; Δ ⊢_c T @ l
            Term::BoxTy(code) => {
                self.meta_layer(env)?;
                let Type::CodeTy { ctx, level } = self.whnf(env, ty)? else {
                    return Err(TypeError::HeadMismatch);
                };
                self.lev_eq(l, &Level::Zero)?;
                self.ty_check(&env.in_ctx(ctx, Layer::Code), code, &level)
            }
            // box t : □(Δ ⊢ T @ l) @ 0 ⟸ Ψ; Δ ⊢_c t : T @ l
            Term::BoxTm(code) => {
                self.meta_layer(env)?;
                let Type::CodeTm { ctx, ty, level } = self.whnf(env, ty)? else {
                    return Err(TypeError::HeadMismatch);
                };
                self.lev_eq(l, &Level::Zero)?;
                self.tm_check(&env.in_ctx(ctx, Layer::Code), code, &ty, &level)
            }
            // Structural descent through binders (box may hide in bodies).
            Term::Lam { dom_level, cod_level, dom, body } => {
                self.not_var_layer(env)?;
                let Type::Pi { dom_level: pd, cod_level: pc, dom: ps, cod: pt } =
                    self.whnf(env, ty)?
                else {
                    return Err(TypeError::HeadMismatch);
                };
                self.level_wf(env, dom_level)?;
                self.level_wf(env, cod_level)?;
                self.lev_eq(dom_level, &pd)?;
                self.lev_eq(cod_level, &pc)?;
                self.lev_eq(l, &Level::max(dom_level.clone(), cod_level.clone()))?;
                self.ty_check(env, dom, dom_level)?;
                self.conv_ty(env, &ps, dom, dom_level)?;
                let e = env.push_entry(Rc::clone(dom), dom_level.clone());
                self.tm_check(&e, body, &pt, cod_level)
            }
            Term::ULam { num_vars, level, body } => {
                self.meta_layer(env)?;
                let Type::UPi { num_vars: pn, level: pl, body: pt } = self.whnf(env, ty)?
                else {
                    return Err(TypeError::HeadMismatch);
                };
                if *num_vars == 0 || *num_vars != pn {
                    return Err(TypeError::UnivArityMismatch);
                }
                self.lev_eq(l, &Level::Omega)?;
                let e = env.push_univs(*num_vars);
                self.level_wf(&e, level)?;
                self.lev_eq(level, &pl)?;
                self.tm_check(&e, body, &pt, level)
            }
            Term::CtxLam { level, body } => {
                self.meta_layer(env)?;
                let Type::CtxPi { level: pl, body: pt } = self.whnf(env, ty)? else {
                    return Err(TypeError::HeadMismatch);
                };
                self.level_wf(env, level)?;
                self.lev_eq(level, &pl)?;
                self.lev_eq(l, level)?;
                let e = env.push_global(GlobalBinding::Ctx);
                self.tm_check(&e, body, &pt, level)
            }
            Term::TyLam { ctx, arg_level, body_level, body } => {
                self.meta_layer(env)?;
                let Type::TyPi { ctx: pctx, arg_level: pal, body_level: pbl, body: pt } =
                    self.whnf(env, ty)?
                else {
                    return Err(TypeError::HeadMismatch);
                };
                self.level_wf(env, arg_level)?;
                self.level_wf(env, body_level)?;
                self.lev_eq(arg_level, &pal)?;
                self.lev_eq(body_level, &pbl)?;
                self.lev_eq(l, body_level)?;
                self.ctx_wf(env, Layer::Prog, ctx)?;
                conv_local_ctx(&env.psi, Layer::Prog, &pctx, ctx, self.fuel)?;
                let e = env.push_global(GlobalBinding::Ty {
                    ctx: ctx.clone(),
                    layer: Layer::Prog,
                    level: arg_level.clone(),
                });
                self.tm_check(&e, body, &pt, body_level)
            }
            _ => {
                let (inferred, li) = self.tm_infer(env, t)?;
                self.lev_eq(l, &li)?;
                self.conv_ty(env, ty, &inferred, l)
            }
        }
    }

    /// `⊢_i t : ? @ ?` — infer the canonical type and level.
    fn tm_infer(&self, env: &Env, t: &Term) -> R<(Type, Level)> {
        match t {
            // The two forms layer v admits.
            Term::Var(x) => {
                let Some(i) = env.gamma.entries.len().checked_sub(1 + x.0 as usize) else {
                    return Err(TypeError::UnboundLocalVar(x.0));
                };
                let e = &env.gamma.entries[i];
                Ok((e.ty.shift_local(x.0 + 1), e.level.clone()))
            }
            Term::GlobalTm { var, subst } => {
                let Some(binding) = lookup(&env.psi, *var) else {
                    return Err(TypeError::UnboundGlobalVar(var.0));
                };
                let GlobalBinding::Tm { ctx, layer, ty, level } = binding else {
                    return Err(TypeError::WrongGlobalBinding(var.0));
                };
                // i' ∈ {v, c} is the binding invariant; i' ≤ i:
                if *layer > env.layer {
                    return Err(TypeError::LayerMismatch);
                }
                let level = level.clone();
                let ctx = ctx.shift_global(var.0 + 1);
                let ty = ty.shift_global(var.0 + 1);
                self.subst_ck(env, subst, &ctx)?;
                Ok((ty.apply_local(subst), level))
            }

            // -- encodings and Nat (layers c/p/m) ---------------------------
            Term::TmNat => {
                self.not_var_layer(env)?;
                Ok((Type::Ty(Level::Zero), Level::constant(1)))
            }
            Term::TmPi { dom_level, cod_level, dom, cod } => {
                self.not_var_layer(env)?;
                self.level_wf(env, dom_level)?;
                self.level_wf(env, cod_level)?;
                self.tm_check(
                    env,
                    dom,
                    &Type::Ty(dom_level.clone()),
                    &Level::succ(dom_level.clone()),
                )?;
                let el = Type::El { level: dom_level.clone(), tm: Rc::clone(dom) };
                let e = env.push_entry(Rc::new(el), dom_level.clone());
                self.tm_check(
                    &e,
                    cod,
                    &Type::Ty(cod_level.clone()),
                    &Level::succ(cod_level.clone()),
                )?;
                let lmax = Level::max(dom_level.clone(), cod_level.clone());
                Ok((Type::Ty(lmax.clone()), Level::succ(lmax)))
            }
            Term::TmTy(l) => {
                self.not_var_layer(env)?;
                self.level_wf(env, l)?;
                Ok((Type::Ty(Level::succ(l.clone())), Level::succ(Level::succ(l.clone()))))
            }
            // Encoding of Id (extension): Id^l (s; t; u) : Ty l.
            Term::TmId { level, ty, lhs, rhs } => {
                self.not_var_layer(env)?;
                self.level_wf(env, level)?;
                self.tm_check(env, ty, &Type::Ty(level.clone()), &Level::succ(level.clone()))?;
                let el = Type::El { level: level.clone(), tm: Rc::clone(ty) };
                self.tm_check(env, lhs, &el, level)?;
                self.tm_check(env, rhs, &el, level)?;
                Ok((Type::Ty(level.clone()), Level::succ(level.clone())))
            }
            // Encoding of Σ (extension): Σ^{l,l'}(x:s).t : Ty (l⊔l').
            Term::TmSigma { fst_level, snd_level, fst, snd } => {
                self.not_var_layer(env)?;
                self.level_wf(env, fst_level)?;
                self.level_wf(env, snd_level)?;
                self.tm_check(
                    env,
                    fst,
                    &Type::Ty(fst_level.clone()),
                    &Level::succ(fst_level.clone()),
                )?;
                let el = Type::El { level: fst_level.clone(), tm: Rc::clone(fst) };
                let e = env.push_entry(Rc::new(el), fst_level.clone());
                self.tm_check(
                    &e,
                    snd,
                    &Type::Ty(snd_level.clone()),
                    &Level::succ(snd_level.clone()),
                )?;
                let lmax = Level::max(fst_level.clone(), snd_level.clone());
                Ok((Type::Ty(lmax.clone()), Level::succ(lmax)))
            }
            // Encodings of Unit/Empty (extension): Unit, Empty : Ty 0.
            Term::TmUnit | Term::TmEmpty => {
                self.not_var_layer(env)?;
                Ok((Type::Ty(Level::Zero), Level::constant(1)))
            }
            Term::Zero => {
                self.not_var_layer(env)?;
                Ok((Type::Nat, Level::Zero))
            }
            Term::Succ(n) => {
                self.not_var_layer(env)?;
                self.tm_check(env, n, &Type::Nat, &Level::Zero)?;
                Ok((Type::Nat, Level::Zero))
            }
            Term::ElimNat { level, motive, base, step, scrut } => {
                self.not_var_layer(env)?;
                self.level_wf(env, level)?;
                let e_x = env.push_entry(Rc::new(Type::Nat), Level::Zero);
                self.ty_check(&e_x, motive, level)?;
                let base_ty =
                    motive.apply_local(&LocalSubst::id(&env.gamma).extended(Rc::new(Term::Zero)));
                self.tm_check(env, base, &base_ty, level)?;
                // M[su x/x] scoped in (Γ, x : Nat, y : M).
                let su_x = Term::Succ(Rc::new(Term::Var(LocalVar(1))));
                let step_ty = motive.apply_local(
                    &LocalSubst::id(&env.gamma).shift_local(2).extended(Rc::new(su_x)),
                );
                let e_xy = e_x.push_entry(Rc::clone(motive), level.clone());
                self.tm_check(&e_xy, step, &step_ty, level)?;
                self.tm_check(env, scrut, &Type::Nat, &Level::Zero)?;
                Ok((
                    motive.apply_local(&LocalSubst::id(&env.gamma).extended(Rc::clone(scrut))),
                    level.clone(),
                ))
            }

            // -- identity (extension beyond ch. 04; kernel-v1-extensions) ---
            // refl^l (S; t) : Id^l (S; t; t) @ l
            Term::Refl { level, ty, tm } => {
                self.not_var_layer(env)?;
                self.level_wf(env, level)?;
                self.ty_check(env, ty, level)?;
                self.tm_check(env, tm, ty, level)?;
                Ok((
                    Type::Id {
                        level: level.clone(),
                        ty: Rc::clone(ty),
                        lhs: Rc::clone(tm),
                        rhs: Rc::clone(tm),
                    },
                    level.clone(),
                ))
            }
            // Based path induction (Paulin-Mohring):
            // J^{l,l'} (S; a; y p. M; c; u; e) : M[u/y, e/p] @ l'.
            Term::J { ty_level, motive_level, ty, lhs, motive, case, rhs, proof } => {
                self.not_var_layer(env)?;
                self.level_wf(env, ty_level)?;
                self.level_wf(env, motive_level)?;
                self.ty_check(env, ty, ty_level)?;
                self.tm_check(env, lhs, ty, ty_level)?;
                // M scoped in (Γ, y : S, p : Id^l(S; a; y)).
                let e_y = env.push_entry(Rc::clone(ty), ty_level.clone());
                let p_ty = Type::Id {
                    level: ty_level.clone(),
                    ty: Rc::new(ty.shift_local(1)),
                    lhs: Rc::new(lhs.shift_local(1)),
                    rhs: Rc::new(Term::Var(LocalVar(0))),
                };
                let e_yp = e_y.push_entry(Rc::new(p_ty), ty_level.clone());
                self.ty_check(&e_yp, motive, motive_level)?;
                // c : M[a/y, refl^l(S; a)/p].
                let refl_a = Term::Refl {
                    level: ty_level.clone(),
                    ty: Rc::clone(ty),
                    tm: Rc::clone(lhs),
                };
                let case_ty = motive.apply_local(
                    &LocalSubst::id(&env.gamma)
                        .extended(Rc::clone(lhs))
                        .extended(Rc::new(refl_a)),
                );
                self.tm_check(env, case, &case_ty, motive_level)?;
                self.tm_check(env, rhs, ty, ty_level)?;
                let id_ty = Type::Id {
                    level: ty_level.clone(),
                    ty: Rc::clone(ty),
                    lhs: Rc::clone(lhs),
                    rhs: Rc::clone(rhs),
                };
                self.tm_check(env, proof, &id_ty, ty_level)?;
                Ok((
                    motive.apply_local(
                        &LocalSubst::id(&env.gamma)
                            .extended(Rc::clone(rhs))
                            .extended(Rc::clone(proof)),
                    ),
                    motive_level.clone(),
                ))
            }

            // -- dependent pairs (extension beyond ch. 04) ------------------
            // pair^{l,l'}(x:S.T; a; b) : Σ^{l,l'}(x:S).T @ l⊔l'.
            Term::Pair { fst_level, snd_level, fst_ty, snd_ty, fst, snd } => {
                self.not_var_layer(env)?;
                self.level_wf(env, fst_level)?;
                self.level_wf(env, snd_level)?;
                self.ty_check(env, fst_ty, fst_level)?;
                let e = env.push_entry(Rc::clone(fst_ty), fst_level.clone());
                self.ty_check(&e, snd_ty, snd_level)?;
                self.tm_check(env, fst, fst_ty, fst_level)?;
                // b : T[a/x].
                let snd_at = snd_ty
                    .apply_local(&LocalSubst::id(&env.gamma).extended(Rc::clone(fst)));
                self.tm_check(env, snd, &snd_at, snd_level)?;
                Ok((
                    Type::Sigma {
                        fst_level: fst_level.clone(),
                        snd_level: snd_level.clone(),
                        fst: Rc::clone(fst_ty),
                        snd: Rc::clone(snd_ty),
                    },
                    Level::max(fst_level.clone(), snd_level.clone()),
                ))
            }
            // fst^{l,l'}(x:S.T; p) : S @ l.
            Term::Fst { fst_level, snd_level, fst_ty, snd_ty, pair } => {
                self.not_var_layer(env)?;
                self.level_wf(env, fst_level)?;
                self.level_wf(env, snd_level)?;
                self.ty_check(env, fst_ty, fst_level)?;
                let e = env.push_entry(Rc::clone(fst_ty), fst_level.clone());
                self.ty_check(&e, snd_ty, snd_level)?;
                let sigma = Type::Sigma {
                    fst_level: fst_level.clone(),
                    snd_level: snd_level.clone(),
                    fst: Rc::clone(fst_ty),
                    snd: Rc::clone(snd_ty),
                };
                self.tm_check(
                    env,
                    pair,
                    &sigma,
                    &Level::max(fst_level.clone(), snd_level.clone()),
                )?;
                Ok(((**fst_ty).clone(), fst_level.clone()))
            }
            // snd^{l,l'}(x:S.T; p) : T[fst p/x] @ l'.
            Term::Snd { fst_level, snd_level, fst_ty, snd_ty, pair } => {
                self.not_var_layer(env)?;
                self.level_wf(env, fst_level)?;
                self.level_wf(env, snd_level)?;
                self.ty_check(env, fst_ty, fst_level)?;
                let e = env.push_entry(Rc::clone(fst_ty), fst_level.clone());
                self.ty_check(&e, snd_ty, snd_level)?;
                let sigma = Type::Sigma {
                    fst_level: fst_level.clone(),
                    snd_level: snd_level.clone(),
                    fst: Rc::clone(fst_ty),
                    snd: Rc::clone(snd_ty),
                };
                self.tm_check(
                    env,
                    pair,
                    &sigma,
                    &Level::max(fst_level.clone(), snd_level.clone()),
                )?;
                let fst_p = Term::Fst {
                    fst_level: fst_level.clone(),
                    snd_level: snd_level.clone(),
                    fst_ty: Rc::clone(fst_ty),
                    snd_ty: Rc::clone(snd_ty),
                    pair: Rc::clone(pair),
                };
                Ok((
                    snd_ty
                        .apply_local(&LocalSubst::id(&env.gamma).extended(Rc::new(fst_p))),
                    snd_level.clone(),
                ))
            }

            // -- unit and empty (extension beyond ch. 04) -------------------
            // ⟨⟩ : Unit @ 0.
            Term::Triv => {
                self.not_var_layer(env)?;
                Ok((Type::Unit, Level::Zero))
            }
            // elim_Empty^l (x. M; t) : M[t/x] @ l.
            Term::ElimEmpty { level, motive, scrut } => {
                self.not_var_layer(env)?;
                self.level_wf(env, level)?;
                let e_x = env.push_entry(Rc::new(Type::Empty), Level::Zero);
                self.ty_check(&e_x, motive, level)?;
                self.tm_check(env, scrut, &Type::Empty, &Level::Zero)?;
                Ok((
                    motive.apply_local(&LocalSubst::id(&env.gamma).extended(Rc::clone(scrut))),
                    level.clone(),
                ))
            }

            // -- dependent functions ----------------------------------------
            Term::Lam { dom_level, cod_level, dom, body } => {
                self.not_var_layer(env)?;
                self.level_wf(env, dom_level)?;
                self.level_wf(env, cod_level)?;
                self.ty_check(env, dom, dom_level)?;
                let e = env.push_entry(Rc::clone(dom), dom_level.clone());
                let (cod, cl) = self.tm_infer(&e, body)?;
                self.lev_eq(cod_level, &cl)?;
                Ok((
                    Type::Pi {
                        dom_level: dom_level.clone(),
                        cod_level: cod_level.clone(),
                        dom: Rc::clone(dom),
                        cod: Rc::new(cod),
                    },
                    Level::max(dom_level.clone(), cod_level.clone()),
                ))
            }
            Term::App { fun, dom_level, cod_level, dom, cod, arg } => {
                self.not_var_layer(env)?;
                self.level_wf(env, dom_level)?;
                self.level_wf(env, cod_level)?;
                self.ty_check(env, dom, dom_level)?;
                let e = env.push_entry(Rc::clone(dom), dom_level.clone());
                self.ty_check(&e, cod, cod_level)?;
                let pi = Type::Pi {
                    dom_level: dom_level.clone(),
                    cod_level: cod_level.clone(),
                    dom: Rc::clone(dom),
                    cod: Rc::clone(cod),
                };
                self.tm_check(
                    env,
                    fun,
                    &pi,
                    &Level::max(dom_level.clone(), cod_level.clone()),
                )?;
                self.tm_check(env, arg, dom, dom_level)?;
                Ok((
                    cod.apply_local(&LocalSubst::id(&env.gamma).extended(Rc::clone(arg))),
                    cod_level.clone(),
                ))
            }

            // -- universe-polymorphic functions (layer m) -------------------
            Term::ULam { num_vars, level, body } => {
                self.meta_layer(env)?;
                if *num_vars == 0 {
                    return Err(TypeError::UnivArityMismatch);
                }
                let e = env.push_univs(*num_vars);
                self.level_wf(&e, level)?;
                let (ty, lt) = self.tm_infer(&e, body)?;
                self.lev_eq(level, &lt)?;
                Ok((
                    Type::UPi {
                        num_vars: *num_vars,
                        level: level.clone(),
                        body: Rc::new(ty),
                    },
                    Level::Omega,
                ))
            }
            Term::UApp { fun, levels } => {
                self.meta_layer(env)?;
                let (fun_ty, fl) = self.tm_infer(env, fun)?;
                self.lev_eq(&fl, &Level::Omega)?;
                let Type::UPi { num_vars, level, body } = self.whnf(env, &fun_ty)? else {
                    return Err(TypeError::HeadMismatch);
                };
                if levels.is_empty() || levels.len() != num_vars as usize {
                    return Err(TypeError::UnivArityMismatch);
                }
                for l in levels {
                    self.level_wf(env, l)?;
                }
                // Written vectors are outermost-first; instantiation wants
                // innermost-first.
                let phi: Vec<Level> = levels.iter().rev().cloned().collect();
                Ok((body.inst_univ(&phi), level.inst_at(&phi, 0)))
            }

            // -- meta-functions (layer m) -----------------------------------
            Term::CtxLam { level, body } => {
                self.meta_layer(env)?;
                self.level_wf(env, level)?;
                let e = env.push_global(GlobalBinding::Ctx);
                let (ty, lt) = self.tm_infer(&e, body)?;
                self.lev_eq(level, &lt)?;
                Ok((Type::CtxPi { level: level.clone(), body: Rc::new(ty) }, level.clone()))
            }
            Term::CtxApp { fun, ctx } => {
                self.meta_layer(env)?;
                let (fun_ty, _) = self.tm_infer(env, fun)?;
                let Type::CtxPi { level, body } = self.whnf(env, &fun_ty)? else {
                    return Err(TypeError::HeadMismatch);
                };
                self.ctx_wf(env, Layer::Prog, ctx)?;
                Ok((
                    body.apply_global(&GlobalSubst::single(GlobalEntry::Ctx(ctx.clone()))),
                    level,
                ))
            }
            Term::TyLam { ctx, arg_level, body_level, body } => {
                self.meta_layer(env)?;
                self.level_wf(env, arg_level)?;
                self.level_wf(env, body_level)?;
                self.ctx_wf(env, Layer::Prog, ctx)?;
                let e = env.push_global(GlobalBinding::Ty {
                    ctx: ctx.clone(),
                    layer: Layer::Prog,
                    level: arg_level.clone(),
                });
                let (ty, lt) = self.tm_infer(&e, body)?;
                self.lev_eq(body_level, &lt)?;
                Ok((
                    Type::TyPi {
                        ctx: ctx.clone(),
                        arg_level: arg_level.clone(),
                        body_level: body_level.clone(),
                        body: Rc::new(ty),
                    },
                    body_level.clone(),
                ))
            }
            Term::TyApp { fun, arg } => {
                self.meta_layer(env)?;
                let (fun_ty, _) = self.tm_infer(env, fun)?;
                let Type::TyPi { ctx, arg_level, body_level, body } =
                    self.whnf(env, &fun_ty)?
                else {
                    return Err(TypeError::HeadMismatch);
                };
                self.ty_check(&env.in_ctx(ctx, Layer::Prog), arg, &arg_level)?;
                Ok((
                    body.apply_global(&GlobalSubst::single(GlobalEntry::Ty(Rc::clone(arg)))),
                    body_level,
                ))
            }

            // -- contextual types (layer m) ---------------------------------
            // box carries neither its context nor its level: checking-only.
            Term::BoxTy(_) | Term::BoxTm(_) => Err(TypeError::NotInferable),

            Term::LetBoxTy { motive_level, code_level, ctx, motive, body, scrut } => {
                self.meta_layer(env)?;
                self.level_wf(env, motive_level)?;
                self.level_wf(env, code_level)?;
                self.ctx_wf(env, Layer::Prog, ctx)?;
                let code_ty =
                    Type::CodeTy { ctx: ctx.clone(), level: code_level.clone() };
                self.tm_check(env, scrut, &code_ty, &Level::Zero)?;
                let e_x = env.push_entry(Rc::new(code_ty), Level::Zero);
                self.ty_check(&e_x, motive, motive_level)?;
                // Body under Ψ, U : Typ_c(Δ, l) at M[box U^id/x_T].
                let e_u = env.push_global(GlobalBinding::Ty {
                    ctx: ctx.clone(),
                    layer: Layer::Code,
                    level: code_level.clone(),
                });
                let box_u = Term::BoxTy(Rc::new(gty(0, &ctx.shift_global(1))));
                let body_ty = motive
                    .shift_global(1)
                    .apply_local(&LocalSubst::id(&e_u.gamma).extended(Rc::new(box_u)));
                self.tm_check(&e_u, body, &body_ty, motive_level)?;
                Ok((
                    motive.apply_local(&LocalSubst::id(&env.gamma).extended(Rc::clone(scrut))),
                    motive_level.clone(),
                ))
            }
            Term::LetBoxTm { motive_level, code_level, ctx, ty, motive, body, scrut } => {
                self.meta_layer(env)?;
                self.level_wf(env, motive_level)?;
                self.level_wf(env, code_level)?;
                self.ctx_wf(env, Layer::Prog, ctx)?;
                self.ty_check(&env.in_ctx(ctx.clone(), Layer::Prog), ty, code_level)?;
                let code_ty = Type::CodeTm {
                    ctx: ctx.clone(),
                    ty: Rc::clone(ty),
                    level: code_level.clone(),
                };
                self.tm_check(env, scrut, &code_ty, &Level::Zero)?;
                let e_x = env.push_entry(Rc::new(code_ty), Level::Zero);
                self.ty_check(&e_x, motive, motive_level)?;
                // Body under Ψ, u : Trm_c(Δ ⊢ T @ l) at M[box u^id/x_t].
                let e_u = env.push_global(GlobalBinding::Tm {
                    ctx: ctx.clone(),
                    layer: Layer::Code,
                    ty: Rc::clone(ty),
                    level: code_level.clone(),
                });
                let box_u = Term::BoxTm(Rc::new(gtm(0, &ctx.shift_global(1))));
                let body_ty = motive
                    .shift_global(1)
                    .apply_local(&LocalSubst::id(&e_u.gamma).extended(Rc::new(box_u)));
                self.tm_check(&e_u, body, &body_ty, motive_level)?;
                Ok((
                    motive.apply_local(&LocalSubst::id(&env.gamma).extended(Rc::clone(scrut))),
                    motive_level.clone(),
                ))
            }

            // -- recursive principles over code (layer m) -------------------
            Term::ElimCodeTy {
                ty_motive_level,
                tm_motive_level,
                motives,
                branches,
                code_level,
                ctx,
                scrut,
            } => {
                self.meta_layer(env)?;
                self.rec_ga(env, motives, branches, ty_motive_level, tm_motive_level)?;
                self.level_wf(env, code_level)?;
                self.ctx_wf(env, Layer::Prog, ctx)?;
                let code_ty =
                    Type::CodeTy { ctx: ctx.clone(), level: code_level.clone() };
                self.tm_check(env, scrut, &code_ty, &Level::Zero)?;
                Ok((
                    inst_ty_motive(
                        &motives.ty_motive,
                        (0, 0, 0),
                        code_level.clone(),
                        ctx.clone(),
                        (**scrut).clone(),
                        &env.gamma,
                    ),
                    ty_motive_level.clone(),
                ))
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
                self.meta_layer(env)?;
                self.rec_ga(env, motives, branches, ty_motive_level, tm_motive_level)?;
                self.level_wf(env, code_level)?;
                self.ctx_wf(env, Layer::Prog, ctx)?;
                self.ty_check(&env.in_ctx(ctx.clone(), Layer::Prog), ty, code_level)?;
                let code_ty = Type::CodeTm {
                    ctx: ctx.clone(),
                    ty: Rc::clone(ty),
                    level: code_level.clone(),
                };
                self.tm_check(env, scrut, &code_ty, &Level::Zero)?;
                Ok((
                    inst_tm_motive(
                        &motives.tm_motive,
                        (0, 0, 0),
                        code_level.clone(),
                        ctx.clone(),
                        (**ty).clone(),
                        (**scrut).clone(),
                        &env.gamma,
                    ),
                    tm_motive_level.clone(),
                ))
            }
        }
    }

    /// The `G_A = G_M G_Typ G_Trm` premise bundle shared by the two
    /// recursor rules: motive levels, both motives well-formed in their
    /// scopes, and all 28 branches at their instantiated motive types.
    fn rec_ga(
        &self,
        env: &Env,
        motives: &crate::term::Motives,
        branches: &crate::term::Branches,
        l1: &Level,
        l2: &Level,
    ) -> R {
        self.level_wf(env, l1)?;
        self.level_wf(env, l2)?;
        let specs = rec::motive_specs(l1, l2);
        for (spec, m) in specs.iter().zip(rec::motive_types(motives)) {
            let e = env.push_spec(&spec.tele);
            self.ty_check(&e, m, &spec.level)?;
        }
        let specs = rec::branch_specs(motives, l1, l2, &env.gamma);
        for (spec, b) in specs.iter().zip(rec::branch_terms(branches)) {
            let e = env.push_spec(&spec.tele);
            self.tm_check(&e, b, &spec.ty, &spec.level)?;
        }
        Ok(())
    }
}
