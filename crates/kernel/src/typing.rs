//! The type checker: syntax-directed checking of the ch. 04 judgments
//! (docs/delam/04) over fully explicit core terms.
//!
//! | tex judgment            | here                                    |
//! |-------------------------|-----------------------------------------|
//! | `⊢_L Ψ`                 | [`check_global_ctx`]                    |
//! | `⊢_L Ψ, Ψ'` from `⊢_L Ψ`| [`check_global_ctx_extension`]          |
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
//! - The recursor rules check the two motives and 56 branches against the
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
//! **What a rule passes to the next.** Not a [`Type`] but an
//! [`ity::ITy`]: syntax, or an un-spelled *description* of a component of
//! something that reduces to a former
//! (`docs/intro-by-type-design.md` §3.2). Every rule but the five checked
//! spellings produces `Syn` and behaves exactly as it did before
//! descriptions existed; `fst@`/`snd@`/`pair@`/`inl@`/`inr@` produce and
//! consume `Sel`, whose point is that the component is never spelled — the
//! object the elaborator used to write into an annotation is `3.5ⁿ` in the
//! nesting as syntax and linear as a value graph, and the checker now names
//! it instead of building it. A description is consumed by exactly two
//! operations, [`Tc::conv_ty`] and [`Tc::view`], each of which evaluates it
//! in a **per-query** value arena and keeps nothing that outlives the query.
//! Where a description must become syntax after all — the four λ inference
//! arms, which wrap the body's inferred type in a `Π`-shaped former —
//! [`Tc::materialize`] runs the rewriter, which is complete, is the answer
//! this checker gave before, and is counted (`crate::stats`'s
//! `ity_materialized`).
//!
//! [`oracle`] is the same checker with every description spelled on
//! formation, and `tests/typing_differential.rs` holds the two to the same
//! verdicts — the compensating control for the weakening, in the shape
//! [`crate::conv::oracle`] established for conversion.
//!
//! **Fuel.** The checker's own recursion is structural, so it terminates
//! without a budget; only conversion and weak-head normalization need one.
//! `fuel` is granted *per conversion call / per normalization* (not shared
//! globally): total work is bounded by `O(nodes · fuel)`. Within one public
//! checking gate, a later byte-for-byte identical cross-head conversion may
//! reuse an earlier success. Failures are never cached, and the gate has one
//! fixed fuel value, so reuse cannot change a verdict. Exhaustion surfaces as
//! [`TypeError::OutOfFuel`], distinct from a mismatch. On well-typed input it
//! means the budget was too small; [`DEFAULT_FUEL`] is a generous default.

use std::cell::{Cell, RefCell};
use std::collections::HashMap;
use std::hash::{Hash, Hasher};
use std::mem::{discriminant, Discriminant};
use std::sync::Arc as Rc;

pub(crate) mod ity;

use ity::{ITy, ITyRef, Sel, SndOf, TyForm};

use crate::conv::{conv_ity_cached, head_ity_cached, ConvError, ITyHead};
#[cfg(not(feature = "value-metrics"))]
use crate::conv::{conv_local_ctx_cached, conv_type_cached};
#[cfg(feature = "value-metrics")]
use crate::conv::{conv_local_ctx_cached_with_metrics, conv_type_cached_with_metrics};
use crate::layer::Layer;
use crate::level::Level;
use crate::rec::{self, gtm, gty, inst_tm_motive, inst_ty_motive, shift_univ_psi};
use crate::reduce::{whnf_type_delta, Defs, GlobalCache, Sig};
use crate::subst::{GlobalEntry, GlobalSubst};
use crate::term::{
    wf_step_telescope, CtxBase, CtxEntries, CtxEntriesIdentity, CtxEntry, GlobalBinding,
    GlobalCtx, GlobalVar, LocalCtx, LocalSubst, LocalVar, SubstTail, Term, Type,
};
use crate::value::ValueMetrics;

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

/// Record how a conversion **miss** ended
/// (`docs/instrumentation-design.md` §2). Exhausted fuel and a genuine
/// mismatch call for opposite responses — more budget against a better
/// spelling — so they never share a column
/// (`issues/generated-proof-cost-diagnostics.md`). Observational: nothing in
/// the kernel reads what this writes.
#[inline]
fn note_conv_outcome(result: &Result<(), ConvError>) {
    match result {
        Ok(()) => {}
        Err(ConvError::OutOfFuel) => crate::stats::conv_out_of_fuel(1),
        Err(ConvError::NotConvertible) => crate::stats::conv_not_convertible(1),
    }
}

// ---------------------------------------------------------------------------
// Public API
// ---------------------------------------------------------------------------

/// `⊢_L Ψ` — well-formedness of a global context under `univs` universe
/// variables.
pub fn check_global_ctx(psi: &GlobalCtx, univs: u32, fuel: u64) -> R {
    let tc = Tc::new(fuel);
    check_global_bindings(&tc, GlobalCtx::default(), psi.bindings.iter(), univs)
}

/// Check an ordered extension of an already well-formed global context.
///
/// This is the safe module-image gate: each binding is checked against the
/// accepted prefix plus every earlier binding in `extension`, without
/// rechecking `prefix` itself. Like the other public checking judgments, it
/// presupposes the well-formedness of its ambient context.
pub fn check_global_ctx_extension(
    prefix: &GlobalCtx,
    extension: &[GlobalBinding],
    univs: u32,
    fuel: u64,
) -> R {
    let tc = Tc::new(fuel);
    check_global_bindings(&tc, prefix.clone(), extension.iter(), univs)
}

fn check_global_bindings<'a>(
    tc: &Tc,
    mut prefix: GlobalCtx,
    bindings: impl IntoIterator<Item = &'a GlobalBinding>,
    univs: u32,
) -> R {
    for b in bindings {
        let env = binding_env(&prefix, univs);
        check_global_binding_declaration(tc, &env, b)?;
        if let GlobalBinding::Tm { ctx, layer, ty, level, body: Some(t) } = b {
            tc.tm_check_rc(&env.in_ctx(ctx.clone(), *layer), t, ty, level)?;
        }
        drop(env);
        prefix.push(b.clone());
    }
    Ok(())
}

fn binding_env(prefix: &GlobalCtx, univs: u32) -> Env {
    Env {
        psi: prefix.clone(),
        cache: Rc::new(GlobalCache::new()),
        gamma: LocalCtx::nil(),
        layer: Layer::Prog,
        univs,
        #[cfg(feature = "value-metrics")]
        value_metrics: None,
    }
}

/// Everything [`check_global_ctx_extension`] asks of one binding **except a
/// definition's body**: the layer, the level, the context and the statement,
/// over `prefix`. A definition's body is then exactly a [`check_term`] of
/// `body : ty @ level` in `ctx` at the binding's own layer over the same
/// prefix, which is the shape a caller can hand to a worker.
fn check_global_binding_declaration(tc: &Tc, env: &Env, b: &GlobalBinding) -> R {
    match b {
        GlobalBinding::Ctx => {}
        GlobalBinding::Ty { ctx, layer, level } => {
            if !matches!(layer, Layer::Code | Layer::Prog) {
                return Err(TypeError::LayerMismatch);
            }
            tc.level_wf(env, level)?;
            tc.ctx_wf(env, Layer::Prog, ctx)?;
        }
        GlobalBinding::Tm { ctx, layer, ty, level, body } => {
            if !matches!(layer, Layer::Var | Layer::Code) {
                return Err(TypeError::LayerMismatch);
            }
            tc.level_wf(env, level)?;
            tc.ctx_wf(env, Layer::Prog, ctx)?;
            tc.ty_check(&env.in_ctx(ctx.clone(), Layer::Prog), ty, level)?;
            // A definition's body (extension): `Ψ_{<i}; Δ ⊢_{i'} t : T @ l`
            // — checked at the binding's *own* layer, which is what makes
            // δ layer-preserving: unfolding `u` at a layer j ≥ i' can only
            // produce a term that was already legal at j. Layer v admits
            // no term but a variable, so a definition there would be a
            // rename with extra steps; reject it and keep `v` meaning
            // exactly what ch. 04 says.
            if body.is_some() && *layer != Layer::Code {
                return Err(TypeError::LayerMismatch);
            }
        }
    }
    Ok(())
}

/// One binding of an extension, **statement only**: what
/// [`check_global_ctx_extension`] checks of `b` over `prefix` before its
/// body. `⊢_L Ψ` is presupposed. A definition's body is left to the caller
/// as a [`check_term`] of `body : ty @ level` in `ctx` at the binding's layer
/// over the same `prefix`; the two together, in order, are the extension
/// check, and a caller that runs the bodies elsewhere (the elaborator's
/// module replay, over its kernel worker pool) gets the same verdicts.
pub fn check_global_binding_statement(
    prefix: &GlobalCtx,
    b: &GlobalBinding,
    univs: u32,
    fuel: u64,
) -> R {
    let tc = Tc::new(fuel);
    check_global_binding_declaration(&tc, &binding_env(prefix, univs), b)
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
        cache: Rc::new(GlobalCache::new()),
        gamma: LocalCtx::nil(),
        layer,
        univs,
        #[cfg(feature = "value-metrics")]
        value_metrics: None,
    };
    Tc::new(fuel).ctx_wf(&env, layer, gamma)
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
    let env = Env {
        psi: psi.clone(), cache: Rc::new(GlobalCache::new()), gamma: gamma.clone(), layer, univs,
        #[cfg(feature = "value-metrics")]
        value_metrics: None,
    };
    Tc::new(fuel).ty_check(&env, ty, level)
}

/// [`check_type`] while accumulating value-machine activity in `metrics`.
/// Instrumentation is observational and does not alter fuel or verdicts.
#[allow(clippy::too_many_arguments)]
pub fn check_type_profiled(
    psi: &GlobalCtx,
    univs: u32,
    layer: Layer,
    gamma: &LocalCtx,
    ty: &Type,
    level: &Level,
    fuel: u64,
    _metrics: &ValueMetrics,
) -> R {
    let env = Env {
        psi: psi.clone(), cache: Rc::new(GlobalCache::new()), gamma: gamma.clone(), layer, univs,
        #[cfg(feature = "value-metrics")]
        value_metrics: Some(_metrics.clone()),
    };
    Tc::new(fuel).ty_check(&env, ty, level)
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
    let env = Env {
        psi: psi.clone(), cache: Rc::new(GlobalCache::new()), gamma: gamma.clone(), layer, univs,
        #[cfg(feature = "value-metrics")]
        value_metrics: None,
    };
    Tc::new(fuel).ty_infer(&env, ty)
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
    crate::stats::check_terms(1);
    let env = Env {
        psi: psi.clone(), cache: Rc::new(GlobalCache::new()), gamma: gamma.clone(), layer, univs,
        #[cfg(feature = "value-metrics")]
        value_metrics: None,
    };
    Tc::new(fuel).tm_check_ty(&env, t, ty, level)
}

/// [`check_term`] while accumulating value-machine activity in `metrics`.
/// Instrumentation is observational and does not alter fuel or verdicts.
#[allow(clippy::too_many_arguments)]
pub fn check_term_profiled(
    psi: &GlobalCtx,
    univs: u32,
    layer: Layer,
    gamma: &LocalCtx,
    t: &Term,
    ty: &Type,
    level: &Level,
    fuel: u64,
    _metrics: &ValueMetrics,
) -> R {
    crate::stats::check_terms(1);
    let env = Env {
        psi: psi.clone(), cache: Rc::new(GlobalCache::new()), gamma: gamma.clone(), layer, univs,
        #[cfg(feature = "value-metrics")]
        value_metrics: Some(_metrics.clone()),
    };
    Tc::new(fuel).tm_check_ty(&env, t, ty, level)
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
    let env = Env {
        psi: psi.clone(), cache: Rc::new(GlobalCache::new()), gamma: gamma.clone(), layer, univs,
        #[cfg(feature = "value-metrics")]
        value_metrics: None,
    };
    let (ty, l) = Tc::new(fuel).tm_infer_syn(&env, t)?;
    Ok(((*ty).clone(), l))
}

/// The **differential oracle**: the checker with its deferred types spelled
/// the moment they are formed (`docs/intro-by-type-design.md` §3.6).
///
/// Not a checking API. Nothing in the kernel calls anything here, and
/// nothing outside a test should — [`check_term`] and its siblings are the
/// checker. This module exists for the same reason [`crate::conv::oracle`]
/// does, one seam further in: stage 1b moved `typing.rs` from "the type a
/// rule passes on is syntax" to "…is a description", and the compensating
/// control for a weakening like that is standing mechanical evidence that
/// the two answers agree.
///
/// Under [`Tc::eager`] every [`ity::ITy::Sel`] is materialized through the
/// rewriter as soon as it would be formed, and the five `@` rules view
/// their annotation through the rewriter too — so this *is* the checker as
/// it stood before descriptions existed, running the same arms on the same
/// input. `tests/typing_differential.rs` runs the pair over `wt.rs`'s
/// well-typed streams with the checked spellings on and requires
/// verdict-for-verdict agreement, which is machine adequacy
/// (`docs/nbe-conversion-design.md` §11.2) applied at the typing seam.
pub mod oracle {
    use super::*;

    /// [`super::check_term`] with every selection spelled.
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
        Tc::eager(fuel).tm_check_ty(&oracle_env(psi, univs, layer, gamma), t, ty, level)
    }

    /// [`super::infer_term`] with every selection spelled.
    pub fn infer_term(
        psi: &GlobalCtx,
        univs: u32,
        layer: Layer,
        gamma: &LocalCtx,
        t: &Term,
        fuel: u64,
    ) -> R<(Type, Level)> {
        let (ty, l) =
            Tc::eager(fuel).tm_infer_syn(&oracle_env(psi, univs, layer, gamma), t)?;
        Ok(((*ty).clone(), l))
    }

    /// [`super::check_type`] with every selection spelled. Type formation
    /// never forms one, so this is the same function twice — it is here so
    /// a test can hold the whole gate, not a hand-picked half of it.
    pub fn check_type(
        psi: &GlobalCtx,
        univs: u32,
        layer: Layer,
        gamma: &LocalCtx,
        ty: &Type,
        level: &Level,
        fuel: u64,
    ) -> R {
        Tc::eager(fuel).ty_check(&oracle_env(psi, univs, layer, gamma), ty, level)
    }

    /// [`super::infer_type`] with every selection spelled.
    pub fn infer_type(
        psi: &GlobalCtx,
        univs: u32,
        layer: Layer,
        gamma: &LocalCtx,
        ty: &Type,
        fuel: u64,
    ) -> R<Level> {
        Tc::eager(fuel).ty_infer(&oracle_env(psi, univs, layer, gamma), ty)
    }

    /// [`super::check_local_ctx`] with every selection spelled.
    pub fn check_local_ctx(
        psi: &GlobalCtx,
        univs: u32,
        layer: Layer,
        gamma: &LocalCtx,
        fuel: u64,
    ) -> R {
        let env = oracle_env(psi, univs, layer, &LocalCtx::nil());
        Tc::eager(fuel).ctx_wf(&env, layer, gamma)
    }

    /// [`super::check_local_subst`] with every selection spelled.
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
        Tc::eager(fuel)
            .subst_ck(&oracle_env(psi, univs, layer, gamma), delta, target)
    }

    fn oracle_env(psi: &GlobalCtx, univs: u32, layer: Layer, gamma: &LocalCtx) -> Env {
        Env {
            psi: psi.clone(),
            cache: Rc::new(GlobalCache::new()),
            gamma: gamma.clone(),
            layer,
            univs,
            #[cfg(feature = "value-metrics")]
            value_metrics: None,
        }
    }
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
    let env = Env {
        psi: psi.clone(), cache: Rc::new(GlobalCache::new()), gamma: gamma.clone(), layer, univs,
        #[cfg(feature = "value-metrics")]
        value_metrics: None,
    };
    Tc::new(fuel).subst_ck(&env, delta, target)
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
    /// Rescoped definition bodies and binding signatures for **this** Ψ
    /// (`reduce::GlobalCache`), shared by every conversion and whnf query of
    /// one gate rather than rebuilt per query
    /// (`docs/conversion-query-arena-pooling-design.md` §3). Inherited by
    /// every scope that keeps Ψ and rebuilt by the one that does not,
    /// `push_tele`.
    cache: Rc<GlobalCache>,
    gamma: LocalCtx,
    layer: Layer,
    univs: u32,
    #[cfg(feature = "value-metrics")]
    value_metrics: Option<ValueMetrics>,
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
        psi.extend(globals);
        Env {
            psi,
            // Ψ changed, so a cached entry's index denotes a different
            // binding: keeping the old cache here — body or signature alike —
            // would be a soundness bug, not a slowdown. Conversion's
            // `push_tele` rebuilds for the same reason.
            cache: Rc::new(GlobalCache::new()),
            gamma: self.gamma.shift_univ(tu).shift_global(tg),
            layer: self.layer,
            univs: self.univs + tu,
            #[cfg(feature = "value-metrics")]
            value_metrics: self.value_metrics.clone(),
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
    /// **The oracle mode** (`docs/intro-by-type-design.md` §3.6). Under it
    /// an [`ITy::Sel`] is spelled the moment it would be formed and the five
    /// `@` rules view their annotation through the rewriter, so the checker
    /// is the one that existed before descriptions did: today's answer, at
    /// today's cost, on the same arms. That is what makes
    /// `tests/typing_differential.rs` test *only* the new thing — that
    /// evaluating a description and rewriting it agree.
    materialize_eagerly: bool,
    /// Successful conversions whose syntax has different outer constructors.
    /// The cache lives for one public kernel gate; identity keys own every `Rc`
    /// they identify, so allocator reuse cannot create an aliasing key.
    conv_memo: RefCell<HashMap<ConvMemoBucket, Vec<ConvMemo>>>,
    conv_memo_entries: Cell<usize>,
    /// The miss sampler's *site* columns (issues/perf-profile-build-target.md):
    /// the variant names of the terms on the checker's own stack, innermost
    /// last, and the innermost term whose type is being compared. Both are
    /// per-gate state on the checker — the value machine's rule that there is
    /// no global or thread-local instrumentation state holds here too — and
    /// are compiled in only with the feature.
    #[cfg(feature = "value-metrics")]
    diag_stack: RefCell<Vec<&'static str>>,
    #[cfg(feature = "value-metrics")]
    diag_term: RefCell<Option<Term>>,
    /// `HEATHER_CONV_QUERY_TRACE`'s sample counter: conversion *queries* of
    /// the traced item that the reflexivity shortcut answered. Per-gate, like
    /// the two above (issues/quoted-component-traversal-remainder.md).
    #[cfg(feature = "value-metrics")]
    query_trace_seen: Cell<u64>,
}

/// `HEATHER_CONV_QUERY_TRACE`'s parsed setting: the item to trace and the
/// sampling stride. Read once — the variable is a diagnosis switch, not a
/// per-query lookup.
#[cfg(feature = "value-metrics")]
struct QueryTraceCfg {
    item: String,
    every: u64,
}

/// `<item>` or `<item>:<N>`. The default stride keeps a multi-million-query
/// item near the 10–50 k lines a `sort | uniq -c` reads comfortably.
#[cfg(feature = "value-metrics")]
fn query_trace_config() -> Option<&'static QueryTraceCfg> {
    static CFG: std::sync::OnceLock<Option<QueryTraceCfg>> = std::sync::OnceLock::new();
    CFG.get_or_init(|| {
        let raw = std::env::var("HEATHER_CONV_QUERY_TRACE").ok()?;
        // Item names contain `::`, so a trailing `:<digits>` is the stride and
        // anything else is part of the name.
        match raw.rsplit_once(':') {
            Some((item, n)) => match n.parse::<u64>() {
                Ok(every) if every > 0 && !item.ends_with(':') => {
                    Some(QueryTraceCfg { item: item.to_string(), every })
                }
                _ => Some(QueryTraceCfg { item: raw, every: 128 }),
            },
            None => Some(QueryTraceCfg { item: raw, every: 128 }),
        }
    })
    .as_ref()
}

/// Pops the checker's diagnostic stack when a `tm_check`/`tm_infer` frame
/// returns (see [`Tc::diag_stack`]).
#[cfg(feature = "value-metrics")]
struct DiagFrame<'t>(&'t Tc);

#[cfg(feature = "value-metrics")]
impl Drop for DiagFrame<'_> {
    fn drop(&mut self) {
        self.0.diag_stack.borrow_mut().pop();
    }
}

struct RcIdentity<T>(Rc<T>);

impl<T> RcIdentity<T> {
    fn new(value: Rc<T>) -> RcIdentity<T> {
        RcIdentity(value)
    }
}

impl<T> Clone for RcIdentity<T> {
    fn clone(&self) -> Self {
        RcIdentity(Rc::clone(&self.0))
    }
}

impl<T> PartialEq for RcIdentity<T> {
    fn eq(&self, other: &Self) -> bool {
        Rc::ptr_eq(&self.0, &other.0)
    }
}

impl<T> Eq for RcIdentity<T> {}

impl<T> Hash for RcIdentity<T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        std::ptr::hash(Rc::as_ptr(&self.0), state);
    }
}

#[derive(Clone, PartialEq, Eq, Hash)]
enum TypeAnchor {
    None,
    Type(RcIdentity<Type>),
    Term(RcIdentity<Term>),
}

#[derive(Clone, PartialEq, Eq, Hash)]
struct ConvMemoBucket {
    expected: Discriminant<Type>,
    inferred: Discriminant<Type>,
    expected_anchor: TypeAnchor,
    inferred_anchor: TypeAnchor,
    psi: RcIdentity<()>,
    gamma: CtxEntriesIdentity,
    gamma_base: Option<u32>,
    layer: Layer,
    univs: u32,
}

struct ConvMemo {
    psi: GlobalCtx,
    gamma: LocalCtx,
    layer: Layer,
    univs: u32,
    expected: Type,
    inferred: Type,
    level: Level,
}

impl Tc {
    fn new(fuel: u64) -> Tc {
        Tc::with_mode(fuel, false)
    }

    /// The differential oracle's checker: [`Tc::new`] with §3.6's mode bit.
    fn eager(fuel: u64) -> Tc {
        Tc::with_mode(fuel, true)
    }

    fn with_mode(fuel: u64, materialize_eagerly: bool) -> Tc {
        Tc {
            fuel,
            materialize_eagerly,
            conv_memo: RefCell::new(HashMap::new()),
            conv_memo_entries: Cell::new(0),
            #[cfg(feature = "value-metrics")]
            diag_stack: RefCell::new(Vec::new()),
            #[cfg(feature = "value-metrics")]
            diag_term: RefCell::new(None),
            #[cfg(feature = "value-metrics")]
            query_trace_seen: Cell::new(0),
        }
    }

    /// Push `t`'s variant name for the sampler's site column; the frame pops
    /// it. `mode` is `"check"` or `"infer"`.
    #[cfg(feature = "value-metrics")]
    fn diag_enter(&self, t: &Term, mode: &'static str) -> DiagFrame<'_> {
        self.diag_stack.borrow_mut().push(term_head(t));
        let _ = mode;
        DiagFrame(self)
    }

    /// The `site:` line alone — the checker's own stack, innermost first.
    /// The one renderer of the one stack; `diag_site` opens with it and the
    /// query trace prints nothing else, because a backtrace per *query* is
    /// three orders of magnitude more output than a backtrace per miss.
    #[cfg(feature = "value-metrics")]
    fn diag_site_stack(&self, depth: usize) -> String {
        let stack = self.diag_stack.borrow();
        stack.iter().rev().take(depth).copied().collect::<Vec<_>>().join(" < ")
    }

    /// The sampler's site excerpt: the checker's stack innermost first, the
    /// innermost compared term (budget-bounded `Debug`), and the elaborator
    /// frames of a backtrace — which name the emission site that wrote the
    /// annotation being paid for, the thing the head-pair table cannot say.
    /// Rendered once per bucket, so the backtrace's cost is paid once.
    #[cfg(feature = "value-metrics")]
    fn diag_site(&self) -> String {
        use std::fmt::Write as _;
        let mut out = String::new();
        let _ = writeln!(out, "site: {}", self.diag_site_stack(16));
        if let Some(t) = self.diag_term.borrow().as_ref() {
            let mut r = format!("{t:?}");
            if r.len() > 600 {
                let cut = r.char_indices().map(|(i, _)| i).take_while(|&i| i <= 600).last().unwrap_or(0);
                r.truncate(cut);
                r.push('…');
            }
            let _ = writeln!(out, "term: {r}");
        }
        let bt = std::backtrace::Backtrace::force_capture().to_string();
        let frames: Vec<&str> = bt
            .lines()
            .map(str::trim)
            .filter(|l| l.contains("heather_elab") && !l.contains("closure"))
            .take(12)
            .collect();
        if !frames.is_empty() {
            let _ = writeln!(out, "elaborator frames:");
            for f in frames {
                let _ = writeln!(out, "  {f}");
            }
        }
        out
    }

    /// `HEATHER_CONV_QUERY_TRACE=<item>[:N]`: every Nth conversion *query* of
    /// that item which the reflexivity shortcut answered, with the site stack
    /// and a bounded size for the type compared. The misses are traced by
    /// `HEATHER_CONV_MISS_TRACE`; on a workload whose gate is a flat cost per
    /// query the misses are a remainder and the queries are the datum
    /// (issues/quoted-component-traversal-remainder.md).
    ///
    /// Unset, this is one `Option` test per query and nothing else.
    #[cfg(feature = "value-metrics")]
    fn query_trace(&self, env: &Env, expected: &Type) {
        let Some(cfg) = query_trace_config() else { return };
        let Some(metrics) = env.value_metrics.as_ref() else { return };
        if !metrics.current_item().is_some_and(|item| *item == *cfg.item) {
            return;
        }
        let n = self.query_trace_seen.get();
        self.query_trace_seen.set(n + 1);
        if n % cfg.every != 0 {
            return;
        }
        // `Debug` is budget-bounded (crates/kernel/src/fmt.rs), so this is a
        // *saturating* size: 512 nodes' worth of characters and no more.
        let size = format!("{expected:?}").len();
        // The address of the compared type. An annotation the elaborator wrote
        // once and shared into many slots is one address seen many times; a
        // term the elaborator wrote out per occurrence is many addresses. That
        // is the round's (a)-against-(d) question, and nothing else in the
        // process can answer it. (A type built on the stack by the rule itself
        // — the `Π` of the `App` rule — reuses stack addresses; those cluster
        // in one high range and the aggregator says so.)
        eprintln!(
            "conv query trace {} {}/{} size={size} at={expected:p} site: {}",
            cfg.item,
            type_head(expected),
            type_head(expected),
            self.diag_site_stack(40),
        );
    }

    // -- premise helpers ----------------------------------------------------

    /// `⊢_L l : Level` (rejects `ω` and out-of-scope variables).
    fn level_wf(&self, env: &Env, l: &Level) -> R {
        if l.well_formed(env.univs) { Ok(()) } else { Err(TypeError::IllFormedLevel) }
    }

    /// `⊢_L l ≈ l' : Level` (as a premise; `ω ≈ ω` only).
    fn lev_eq(&self, a: &Level, b: &Level) -> R {
        if a.equiv(b) { Ok(()) } else { Err(TypeError::LevelMismatch) }
    }

    /// The conversion rule: `⊢_typeof(i) T ≈ T' @ l`, over the checker's
    /// **descriptions** (`docs/intro-by-type-design.md` §3.3).
    ///
    /// The reflexivity shortcut is structural `==` on [`ITy`]: on two `Syn`s
    /// it is the α-test it has always been, and two equal selections are the
    /// same type by Determinacy. A query with a selection on either side
    /// skips the cross-head memo — the memo's bucket key is built from a
    /// `Type`'s outer constructor and anchor, a selection has neither, and
    /// keeping the key exactly as it was is what makes the counters on an
    /// `@`-free declaration identical to the unit. Such a query goes
    /// straight to [`conv_ity_cached`], whose arena is this query's, as
    /// `conv_type_cached`'s always was.
    fn conv_ty(&self, env: &Env, expected: ITyRef, inferred: ITyRef, l: &Level) -> R {
        // `Conv::ty_root` spends one unit before the same syntactic
        // reflexivity test. Preserve that exact zero-fuel boundary while
        // avoiding an arena for the overwhelmingly common positive case.
        if self.fuel > 0 && expected == inferred {
            crate::stats::conv_shortcut_hits(1);
            #[cfg(feature = "value-metrics")]
            if let Some(e) = expected.as_syn() {
                self.query_trace(env, e);
            }
            return Ok(());
        }
        let (Some(expected), Some(inferred)) = (expected.as_syn(), inferred.as_syn())
        else {
            return self.conv_ity(env, expected, inferred, l);
        };
        // Cross-head conversions necessarily do semantic work before they can
        // succeed and are the repeated family this cache is meant to serve.
        // Same-head judgments are left alone: broad memoization makes large,
        // mostly-distinct inference workloads pay for linear bucket searches.
        let expected_head = discriminant(expected);
        let inferred_head = discriminant(inferred);
        let bucket_key = (expected_head != inferred_head).then(|| ConvMemoBucket {
            expected: expected_head,
            inferred: inferred_head,
            expected_anchor: type_anchor(expected),
            inferred_anchor: type_anchor(inferred),
            psi: RcIdentity::new(env.psi.bindings.identity()),
            gamma: env.gamma.entries.identity(),
            gamma_base: match env.gamma.base {
                CtxBase::Nil => None,
                CtxBase::Var(g) => Some(g.0),
            },
            layer: env.layer,
            univs: env.univs,
        });
        if bucket_key.as_ref().is_some_and(|bucket_key| {
            self
                .conv_memo
                .borrow()
                .get(bucket_key)
                .is_some_and(|bucket| {
                    bucket.iter().any(|entry| {
                        entry.layer == env.layer
                            && entry.univs == env.univs
                            && entry.level == *l
                            && entry.psi.bindings.same_identity(&env.psi.bindings)
                            && entry.gamma == env.gamma
                            && entry.expected == *expected
                            && entry.inferred == *inferred
                    })
                })
        })
        {
            crate::stats::conv_memo_hits(1);
            return Ok(());
        }
        crate::stats::conv_misses(1);
        let at = env.layer.type_layer();
        #[cfg(feature = "value-metrics")]
        {
            // The miss sampler (issues/perf-profile-build-target.md): every
            // query reaching here missed both shortcuts above, and what it
            // then costs is what the elaborator's spelling choices are paid
            // for. Bucketed by head pair, so "El^δ against an inline Σ" and
            // "Sum against Sum" are separate rows with their own clocks.
            let started = std::time::Instant::now();
            let result = conv_type_cached_with_metrics(
                &env.psi,
                &env.gamma,
                at,
                expected,
                inferred,
                l,
                self.fuel,
                env.value_metrics.as_ref(),
                Rc::clone(&env.cache),
            );
            if let Some(metrics) = env.value_metrics.as_ref() {
                let ns = started.elapsed().as_nanos() as u64;
                metrics.record_conv_miss(
                    (type_head(expected), type_head(inferred)),
                    ns,
                    || format!("{}{}", self.diag_site(), first_difference_excerpt(expected, inferred)),
                );
                // `HEATHER_CONV_MISS_TRACE=<item>`: every miss of that one
                // item, with its site and excerpt, where the table keeps one
                // excerpt per head pair. A diagnosis switch under the feature.
                if let Some(item) = metrics.current_item()
                    && std::env::var_os("HEATHER_CONV_MISS_TRACE").is_some_and(|want| *want == *item.as_ref())
                {
                    eprintln!("conv miss trace {item} {}/{} {:.3}ms\n{}{}", type_head(expected), type_head(inferred),
                        ns as f64 / 1e6, self.diag_site(), first_difference_excerpt(expected, inferred));
                }
            }
            note_conv_outcome(&result);
            result?;
        }
        #[cfg(not(feature = "value-metrics"))]
        {
            let result = conv_type_cached(
                &env.psi, &env.gamma, at, expected, inferred, l, self.fuel, Rc::clone(&env.cache),
            );
            note_conv_outcome(&result);
            result?;
        }
        // A gate-wide cap bounds adversarial all-distinct input. Once full,
        // misses retain the ordinary checker behavior rather than evicting a
        // potentially hot positive judgment.
        if let Some(bucket_key) = bucket_key.filter(|_| self.conv_memo_entries.get() < 4096) {
            let mut memo = self.conv_memo.borrow_mut();
            let bucket = memo.entry(bucket_key).or_default();
            // The anchors are deliberately shallow, so unrelated judgments
            // can collide. Keep a miss bounded instead of letting an
            // adversarial bucket turn conversion checking quadratic.
            if bucket.len() < 4 {
                bucket.push(ConvMemo {
                    psi: env.psi.clone(),
                    gamma: env.gamma.clone(),
                    layer: env.layer,
                    univs: env.univs,
                    expected: expected.clone(),
                    inferred: inferred.clone(),
                    level: l.clone(),
                });
                self.conv_memo_entries.set(self.conv_memo_entries.get() + 1);
            }
        }
        Ok(())
    }

    /// The miss of a query with a selection on either side: both
    /// descriptions evaluated in **one per-query arena** and compared by the
    /// ordinary conversion arms (`docs/intro-by-type-design.md` §3.3).
    fn conv_ity(&self, env: &Env, expected: ITyRef, inferred: ITyRef, l: &Level) -> R {
        // Reached only when at least one side is a selection, so this is the
        // `@`-form path and nothing here is on the per-node constant. A side
        // that is a bare spelling never is a selection, so the borrow it is
        // held behind has no `ITy` and one is built here — the one place the
        // borrowing currency has to pay anything back.
        let (own_e, own_i);
        let expected = match expected.as_ity() {
            Some(t) => t,
            None => {
                own_e = ITy::Syn(Rc::new(expected.as_syn().expect("not a selection").clone()));
                &own_e
            }
        };
        let inferred = match inferred.as_ity() {
            Some(t) => t,
            None => {
                own_i = ITy::Syn(Rc::new(inferred.as_syn().expect("not a selection").clone()));
                &own_i
            }
        };
        crate::stats::conv_misses(1);
        let at = env.layer.type_layer();
        let result = conv_ity_cached(
            &env.psi,
            &env.gamma,
            at,
            expected,
            inferred,
            l,
            self.fuel,
            #[cfg(feature = "value-metrics")]
            env.value_metrics.as_ref(),
            Rc::clone(&env.cache),
        );
        note_conv_outcome(&result);
        result?;
        Ok(())
    }

    /// `T ⇝* W` under the checker's budget. δ-transparent unconditionally:
    /// a *type* lives at `typeof(i)`, which is always a computing layer, so
    /// exposing a former from behind a definition is p's business even
    /// while the term being checked is at c.
    fn whnf_syn(&self, env: &Env, t: &Type) -> R<Type> {
        whnf_type_delta(t, &env.gamma, Defs::transparent_cached(&env.psi, &env.cache), self.fuel)
            .map_err(|_| TypeError::OutOfFuel)
    }

    /// [`Tc::whnf_syn`] of a description. A `Syn` is the rewriter, exactly as
    /// before; a selection is spelled first, and paying for that is the
    /// point of [`crate::stats`]'s `ity_materialized`.
    fn whnf(&self, env: &Env, t: ITyRef) -> R<Type> {
        match t.as_syn() {
            Some(t) => self.whnf_syn(env, t),
            None => {
                let t = self.materialize(env, t.as_ity().expect("a selection"))?;
                self.whnf_syn(env, &t)
            }
        }
    }

    /// **Spell a description** (`docs/intro-by-type-design.md` §3.5): whnf
    /// the `of` through the rewriter and take the component's syntax.
    ///
    /// This is the current checker's answer — which is why it is complete
    /// and why it is never silently wrong — and it is exponential exactly
    /// where the current checker is. Its callers are the four λ inference
    /// arms, which must put a `Type` inside a `Π`/`ΠΠ`/`Πg`/`ΠU`, and the
    /// "other formers" branch of [`Tc::view`]. Unlike the value domain the
    /// rewriter is a *syntax* machine, so each step is run in the Γ its
    /// input is scoped in — the prefix `Sel::of_depth` names — rather than
    /// in the ambient one.
    fn materialize(&self, env: &Env, t: &ITy) -> R<Rc<Type>> {
        match t {
            ITy::Syn(t) => Ok(Rc::clone(t)),
            ITy::Owned(t) => Ok(Rc::new(t.clone())),
            ITy::Sel { of, sel, at_depth } => {
                crate::stats::ity_materialized(1);
                let of_depth = sel.of_depth(*at_depth);
                let base = self.materialize(env, of)?;
                let gamma = if of_depth == env.gamma.entries.len() as u32 {
                    env.gamma.clone()
                } else {
                    env.gamma.prefix(of_depth as usize)
                };
                let w = whnf_type_delta(
                    &base,
                    &gamma,
                    Defs::transparent_cached(&env.psi, &env.cache),
                    self.fuel,
                )
                .map_err(|_| TypeError::OutOfFuel)?;
                let picked = match (&w, sel) {
                    (Type::Sigma { fst, .. }, Sel::Fst) => Rc::clone(fst),
                    (Type::Sigma { snd, .. }, Sel::Snd(a)) => Rc::new(
                        snd.apply_local(&LocalSubst::id(&gamma).extended(Rc::clone(a))),
                    ),
                    (Type::Sum { lhs, .. }, Sel::Lhs) => Rc::clone(lhs),
                    (Type::Sum { rhs, .. }, Sel::Rhs) => Rc::clone(rhs),
                    (Type::Pi { dom, .. }, Sel::Dom) => Rc::clone(dom),
                    (Type::Pi { cod, .. }, Sel::Cod) => Rc::clone(cod),
                    // The rule that formed the description had already
                    // viewed `of` and found the former, so this is the two
                    // engines disagreeing, which is a mismatch.
                    _ => return Err(TypeError::HeadMismatch),
                };
                Ok(picked)
            }
        }
    }

    /// [`Tc::view`] in the **syntax** domain: whnf through the rewriter and
    /// read the former off. Split out of [`Tc::view`] so a borrowed expected
    /// type that is a bare spelling — which is never a selection, so its view
    /// is never the value one — reaches it without an [`ITy`] having to
    /// exist.
    fn view_syn(&self, env: &Env, t: ITyRef) -> R<TyForm> {
        Ok(match self.whnf(env, t)? {
            Type::Pi { dom_level, cod_level, dom, cod } => TyForm::Pi {
                dom_level,
                cod_level,
                dom: ITy::Syn(dom),
                cod: ITy::Syn(cod),
            },
            Type::Sigma { fst_level, snd_level, fst, snd } => TyForm::Sigma {
                fst_level,
                snd_level,
                fst: ITy::Syn(fst),
                snd: SndOf::Syn(snd),
            },
            Type::Sum { lhs_level, rhs_level, lhs, rhs } => TyForm::Sum {
                lhs_level,
                rhs_level,
                lhs: ITy::Syn(lhs),
                rhs: ITy::Syn(rhs),
            },
            _ => TyForm::Other,
        })
    }

    /// **The view** (`docs/intro-by-type-design.md` §3.3): the head former of
    /// a description, with its components as descriptions.
    ///
    /// `value_domain` decides which machine answers, and the rule it
    /// encodes is stated once in the design: *the rewriter never runs on a
    /// type that came through an `@` annotation or a selection.* So the λ
    /// checking descent passes `true` only for a selection, the five `@`
    /// rules pass `true` for their annotation even though it is syntax, and
    /// the eager mode passes `false` everywhere — which is what makes it
    /// today's checker.
    ///
    /// In the value domain the head and the levels are read and **the value
    /// is discarded**; nothing the checker keeps outlives the arena. Only
    /// `Π`, `Σ` and `+` get components, because they are the only formers a
    /// checking rule descends into; every other head is
    /// [`TyForm::Other`] and the caller answers `HeadMismatch`.
    fn view(&self, env: &Env, t: &ITy, value_domain: bool) -> R<TyForm> {
        let depth = env.gamma.entries.len() as u32;
        if !value_domain {
            return self.view_syn(env, t.as_ref());
        }
        let head = head_ity_cached(
            &env.psi,
            &env.gamma,
            env.layer.type_layer(),
            t,
            self.fuel,
            #[cfg(feature = "value-metrics")]
            env.value_metrics.as_ref(),
            Rc::clone(&env.cache),
        )?;
        Ok(match head {
            ITyHead::Pi(dom_level, cod_level) => TyForm::Pi {
                dom_level,
                cod_level,
                dom: ITy::Sel { of: Rc::new(t.clone()), sel: Sel::Dom, at_depth: depth },
                // The codomain is the one component scoped one binder deeper
                // than its `of`.
                cod: ITy::Sel { of: Rc::new(t.clone()), sel: Sel::Cod, at_depth: depth + 1 },
            },
            ITyHead::Sigma(fst_level, snd_level) => TyForm::Sigma {
                fst_level,
                snd_level,
                fst: ITy::Sel { of: Rc::new(t.clone()), sel: Sel::Fst, at_depth: depth },
                snd: SndOf::Sel(Rc::new(t.clone()), depth),
            },
            ITyHead::Sum(lhs_level, rhs_level) => TyForm::Sum {
                lhs_level,
                rhs_level,
                lhs: ITy::Sel { of: Rc::new(t.clone()), sel: Sel::Lhs, at_depth: depth },
                rhs: ITy::Sel { of: Rc::new(t.clone()), sel: Sel::Rhs, at_depth: depth },
            },
            ITyHead::Other => TyForm::Other,
        })
    }

    /// [`Tc::view`] of an expected type a *checking* rule is descending
    /// through: the rewriter unless it is a selection (§3.3).
    fn view_expected(&self, env: &Env, t: ITyRef) -> R<TyForm> {
        match t.as_ity() {
            Some(t) => self.view(env, t, !t.is_syn() && !self.materialize_eagerly),
            // A bare spelling is syntax, so `!is_syn()` is false and the view
            // is the syntactic one — reached without building an `ITy`.
            None => self.view_syn(env, t),
        }
    }

    /// [`Tc::view`] of an `@` form's annotation (§3.4): the value domain,
    /// even though the annotation is syntax — that is the whole point of the
    /// form.
    fn view_at(&self, env: &Env, t: &Rc<Type>) -> R<(ITy, TyForm)> {
        let t = ITy::Syn(Rc::clone(t));
        let form = self.view(env, &t, !self.materialize_eagerly)?;
        Ok((t, form))
    }

    /// Reject everything at layer v except the forms listed in ch. 04's
    /// "Note on Layer v Rules".
    fn not_var_layer(&self, env: &Env) -> R {
        if env.layer == Layer::Var { Err(TypeError::LayerMismatch) } else { Ok(()) }
    }

    /// Reject everything but the computing layers p and m. The checked
    /// spellings' guard (`docs/intro-by-type-design.md` §2.3): stronger than
    /// [`Tc::not_var_layer`], which admits layer c, because a form layer c
    /// admits is a form the code recursors must range over.
    fn computing_layer(&self, env: &Env) -> R {
        if env.layer.computes() { Ok(()) } else { Err(TypeError::LayerMismatch) }
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
        // Each entry is checked in the prefix it is scoped in. Grown as we
        // go rather than re-derived per `k`: `Γ` is a spine, so taking the
        // prefix of length `k` walks `|Γ| - k` cells and the loop would be
        // quadratic in `|Γ|` for no reason.
        let mut prefix = LocalCtx { base: gamma.base, entries: CtxEntries::empty() };
        for entry in &gamma.entries {
            let e = env.in_ctx(prefix.clone(), layer);
            self.level_wf(&e, &entry.level)?;
            self.ty_check(&e, &entry.ty, &entry.level)?;
            prefix = prefix.extended(Rc::clone(&entry.ty), entry.level.clone());
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
            self.tm_check_ty(env, &delta.terms[k], &ty, &entry.level)?;
        }
        Ok(())
    }

    // -- types --------------------------------------------------------------

    /// `⊢_i T @ l` for a given `l`: infer the canonical level and compare
    /// (the level-conversion rule).
    ///
    /// **Every type has exactly one level, and it must stay that way.** DeLaM
    /// ch. 04 §Non-cumulativity makes this load-bearing rather than tidy: the
    /// code eliminator must reconstruct code from its components in each
    /// branch, which is only expressible when each term has a unique type —
    /// and `box T : □(Δ ⊢ Ty l)` checks `T` at `l` through this function, so
    /// a type checking at two levels is a *term* with two types. The `ty_ty`
    /// branch of `rec.rs` binds a universe precisely because `Ty ℓ`'s level
    /// varies; `ty_unit` binds none because `Unit`'s does not.
    ///
    /// This is why the obvious repair for the `Vec^l(T;0) ⇝ Unit` level drop
    /// — letting `Unit`/`Empty` check at any level — is **wrong**, and is not
    /// applied here. See `issues/unit-level-and-vec-preservation.md`.
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
                Ok(Level::join(dom_level.clone(), cod_level.clone()))
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
                self.tm_check_ty(env, tm, &Type::Ty(level.clone()), &Level::succ(level.clone()))?;
                Ok(level.clone())
            }
            // Id-formation (extension beyond ch. 04; kernel-v1-extensions):
            // ⊢_i Id^l (S; t; u) @ l ⟸ ⊢_i S @ l, ⊢_i t : S @ l, ⊢_i u : S @ l
            Type::Id { level, ty, lhs, rhs } => {
                self.level_wf(env, level)?;
                self.ty_check(env, ty, level)?;
                self.tm_check_rc(env, lhs, ty, level)?;
                self.tm_check_rc(env, rhs, ty, level)?;
                Ok(level.clone())
            }
            // sEq-formation (extension; docs/sprop-design.md §2.1) — Id's
            // rule verbatim:
            // ⊢_i sEq^l(I; a; b) @ l ⟸ ⊢_i I @ l, ⊢_i a : I @ l, ⊢_i b : I @ l
            Type::SEq { level, ty, lhs, rhs } => {
                self.level_wf(env, level)?;
                self.ty_check(env, ty, level)?;
                self.tm_check_rc(env, lhs, ty, level)?;
                self.tm_check_rc(env, rhs, ty, level)?;
                Ok(level.clone())
            }
            // sEmpty-formation (extension; docs/sprop-design.md §2.2):
            // ⊢_i sEmpty^l @ l — premise-free like Unit/Empty.
            Type::SEmpty { level } => {
                self.level_wf(env, level)?;
                Ok(level.clone())
            }
            Type::Squash { level, ty } => {
                self.level_wf(env, level)?;
                self.ty_check(env, ty, level)?;
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
                Ok(Level::join(fst_level.clone(), snd_level.clone()))
            }
            // Unit/Empty-formation (extension beyond ch. 04):
            // ⊢_i Unit^l @ l, ⊢_i Empty^l @ l.
            //
            // **Level-indexed, not level-polymorphic.** `Unit^l` and
            // `Unit^{l'}` are distinct types, so a type still determines its
            // level and `ty_check` needs no special case — see its doc
            // comment and `docs/unit-empty-level-indexing.md`.
            Type::Unit { level } | Type::Empty { level } => {
                self.level_wf(env, level)?;
                Ok(level.clone())
            }
            // Sum-formation (extension beyond ch. 04; kernel-v1-extensions):
            // ⊢_i A +^{l,l'} B @ l⊔l' ⟸ ⊢_i A @ l, ⊢_i B @ l'. Non-dependent:
            // both summands live in Γ.
            Type::Sum { lhs_level, rhs_level, lhs, rhs } => {
                self.level_wf(env, lhs_level)?;
                self.level_wf(env, rhs_level)?;
                self.ty_check(env, lhs, lhs_level)?;
                self.ty_check(env, rhs, rhs_level)?;
                Ok(Level::join(lhs_level.clone(), rhs_level.clone()))
            }
            // W-formation (extension beyond ch. 04; kernel-v1-extensions):
            // ⊢_i W^{l,l'}(x:S).T @ l⊔l' ⟸ ⊢_i S @ l, (Γ, x:S) ⊢_i T @ l'
            Type::W { shape_level, pos_level, shape, pos } => {
                self.level_wf(env, shape_level)?;
                self.level_wf(env, pos_level)?;
                self.ty_check(env, shape, shape_level)?;
                let e = env.push_entry(Rc::clone(shape), shape_level.clone());
                self.ty_check(&e, pos, pos_level)?;
                Ok(Level::join(shape_level.clone(), pos_level.clone()))
            }
            // Vec-formation (extension; docs/wf-former-design.md §1.1):
            // ⊢_i Vec^l(T; k) @ l ⟸ ⊢_i T @ l, ⊢_i k : Nat @ 0. The length
            // is a term in Γ (no binder), which is what lets the tuple's
            // arity be *computed* from a shape.
            Type::Vec { level, elem, len } => {
                self.level_wf(env, level)?;
                self.ty_check(env, elem, level)?;
                self.tm_check_ty(env, len, &Type::Nat, &Level::Zero)?;
                Ok(level.clone())
            }
            // Fin-formation (extension; §1.2): ⊢_i Fin(k) @ 0 ⟸ ⊢_i k : Nat.
            Type::Fin { len } => {
                self.tm_check_ty(env, len, &Type::Nat, &Level::Zero)?;
                Ok(Level::Zero)
            }
            // Wf-formation (extension; §1.3): ⊢_i Wf^l(x:S). n @ l ⟸
            // ⊢_i S @ l, (Γ, x:S) ⊢_i n : Nat. The arity is a *term*, so it
            // contributes no level — unlike `W`, whose positions are a type.
            Type::Wf { level, shape, arity } => {
                self.level_wf(env, level)?;
                self.ty_check(env, shape, level)?;
                let e_x = env.push_entry(Rc::clone(shape), level.clone());
                self.tm_check_ty(&e_x, arity, &Type::Nat, &Level::Zero)?;
                Ok(level.clone())
            }
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
                crate::stats::global_ref_rescopes(1);
                let sig = env.cache.sig_or_insert(*var, || Sig {
                    ctx: ctx.shift_global(var.0 + 1),
                    ty: None,
                });
                self.subst_ck(env, subst, &sig.ctx)?;
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
    fn tm_check(&self, env: &Env, t: &Term, ty: ITyRef, l: &Level) -> R {
        #[cfg(feature = "value-metrics")]
        let _frame = self.diag_enter(t, "check");
        self.tm_check_inner(env, t, ty, l)
    }

    /// [`Tc::tm_check`] where the caller already holds the expected type as
    /// shared syntax — every rule but the checked spellings.
    ///
    /// The two wrappers exist so the rules can keep spelling their expected
    /// type the way each already holds it; both now **construct nothing**
    /// (`issues/ity-widens-the-checker-per-node-constant.md`). Between them
    /// they are 86 call sites, so what they build lands 86 times in their
    /// callers' frames — and until the checking direction started borrowing,
    /// this one also paid an `Arc` increment and decrement per checked
    /// subterm.
    #[inline(always)]
    fn tm_check_rc(&self, env: &Env, t: &Term, ty: &Rc<Type>, l: &Level) -> R {
        self.tm_check(env, t, ITyRef::Syn(ty), l)
    }

    /// [`Tc::tm_check`] where the rule built the expected type itself and
    /// still owns it — see [`Tc::tm_check_rc`] for why neither copies it.
    #[inline(always)]
    fn tm_check_ty(&self, env: &Env, t: &Term, ty: &Type, l: &Level) -> R {
        self.tm_check(env, t, ITyRef::Syn(ty), l)
    }

    /// The checking λ — the one *checking* descent whose expected type may
    /// be a selection (`docs/intro-by-type-design.md` §3.3): a λ checked at
    /// `Sel { T, Fst }` because it is the first field of a `pair@`. Hence
    /// the view, and hence `Sel::Dom` / `Sel::Cod` existing at all.
    ///
    /// **Outlined deliberately, and measured**
    /// (`issues/ity-widens-the-checker-per-node-constant.md`). It is the one
    /// arm that takes a [`TyForm`] — 200 bytes, two [`ITy`] components it
    /// then holds across its own recursive descent — while the arm the
    /// checker actually recurses *through*, once per term node, is the
    /// fall-through below. Left in [`Tc::tm_check_inner`] those temporaries
    /// sit in every frame of the recursion cycle whether or not a λ is being
    /// checked, and the stack row counts them.
    #[inline(never)]
    fn tm_check_lam(
        &self,
        env: &Env,
        dom_level: &Level,
        cod_level: &Level,
        dom: &Rc<Type>,
        body: &Rc<Term>,
        ty: ITyRef,
        l: &Level,
    ) -> R {
        self.not_var_layer(env)?;
        let TyForm::Pi { dom_level: pd, cod_level: pc, dom: ps, cod: pt } =
            self.view_expected(env, ty)?
        else {
            return Err(TypeError::HeadMismatch);
        };
        self.level_wf(env, dom_level)?;
        self.level_wf(env, cod_level)?;
        self.lev_eq(dom_level, &pd)?;
        self.lev_eq(cod_level, &pc)?;
        self.lev_eq(l, &Level::join(dom_level.clone(), cod_level.clone()))?;
        self.ty_check(env, dom, dom_level)?;
        self.conv_ty(env, ps.as_ref(), ITyRef::Syn(dom), dom_level)?;
        let e = env.push_entry(Rc::clone(dom), dom_level.clone());
        self.tm_check(&e, body, pt.as_ref(), cod_level)
    }

    fn tm_check_inner(&self, env: &Env, t: &Term, ty: ITyRef, l: &Level) -> R {
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
                self.tm_check_rc(&env.in_ctx(ctx, Layer::Code), code, &ty, &level)
            }
            // Structural descent through binders (box may hide in bodies).
            Term::Lam { dom_level, cod_level, dom, body } =>
                self.tm_check_lam(env, dom_level, cod_level, dom, body, ty, l),
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
                self.tm_check_rc(&e, body, &pt, level)
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
                self.tm_check_rc(&e, body, &pt, level)
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
                #[cfg(feature = "value-metrics")]
                conv_local_ctx_cached_with_metrics(
                    &env.psi,
                    Layer::Prog,
                    &pctx,
                    ctx,
                    self.fuel,
                    env.value_metrics.as_ref(),
                    Rc::clone(&env.cache),
                )?;
                #[cfg(not(feature = "value-metrics"))]
                conv_local_ctx_cached(
                    &env.psi, Layer::Prog, &pctx, ctx, self.fuel, Rc::clone(&env.cache),
                )?;
                let e = env.push_global(GlobalBinding::Ty {
                    ctx: ctx.clone(),
                    layer: Layer::Prog,
                    level: arg_level.clone(),
                });
                self.tm_check_rc(&e, body, &pt, body_level)
            }
            _ => {
                let (inferred, li) = self.tm_infer(env, t)?;
                self.lev_eq(l, &li)?;
                // A shallow clone (`Rc` children): the sampler's innermost
                // term, for the site excerpt.
                #[cfg(feature = "value-metrics")]
                {
                    *self.diag_term.borrow_mut() = Some(t.clone());
                }
                self.conv_ty(env, ty, inferred.as_ref(), l)
            }
        }
    }

    /// `⊢_i t : ? @ ?` — infer the canonical type and level.
    ///
    /// **`inline(always)` is load-bearing, and measured**
    /// (`issues/ity-widens-the-checker-per-node-constant.md`). Before stage
    /// 1b this was a tail call with its callee's own signature, so LLVM
    /// merged the two; the `@` dispatch and the `ITy::Owned` wrap made it a
    /// non-tail call, and it fell out of line — putting a fresh 96-byte
    /// frame *and* two 96-byte copies of the inferred `(type, level)` on the
    /// checker's recursion cycle, once per term node. The wrap itself is
    /// free: `ITy` is 72 bytes, exactly `Type`'s, because the tag rides in a
    /// niche.
    #[inline(always)]
    fn tm_infer(&self, env: &Env, t: &Term) -> R<(ITy, Level)> {
        #[cfg(feature = "value-metrics")]
        let _frame = self.diag_enter(t, "infer");
        // The checked spellings are the only rules whose inferred type may
        // be a *description* (`docs/intro-by-type-design.md` §3.2), so they
        // have their own dispatch and every other rule keeps returning
        // syntax — which is the sentence "no existing rule constructs a
        // `Sel`" made true by construction rather than by review.
        if matches!(
            t,
            Term::PairAt { .. }
                | Term::InlAt { .. }
                | Term::InrAt { .. }
                | Term::FstAt { .. }
                | Term::SndAt { .. }
        ) {
            return self.tm_infer_at(env, t);
        }
        let (ty, l) = self.tm_infer_inner(env, t)?;
        Ok((ITy::Owned(ty), l))
    }

    /// [`Tc::tm_infer`] with the inferred type **spelled**: the four λ
    /// inference arms, which have to put it inside a syntactic former, and
    /// the public [`infer_term`]. See [`Tc::materialize`].
    fn tm_infer_syn(&self, env: &Env, t: &Term) -> R<(Rc<Type>, Level)> {
        let (ty, l) = self.tm_infer(env, t)?;
        Ok((self.materialize(env, &ty)?, l))
    }

    /// The five **checked spellings** (`docs/intro-by-type-design.md` §3.4)
    /// — the only inference rules whose result may be an un-spelled
    /// selection, and therefore the only ones that live outside
    /// [`Tc::tm_infer_inner`]. Keeping them here is what makes §3.2's
    /// "no existing rule constructs a `Sel`" a property of the code rather
    /// than of a review: every other arm returns a `Type` and
    /// [`Tc::tm_infer`] wraps it.
    fn tm_infer_at(&self, env: &Env, t: &Term) -> R<(ITy, Level)> {
        match t {
                // -- checked spellings (extension; docs/intro-by-type-design.md)
                //
                // `pair@(T; a; b)`, `inl@`, `inr@`, `fst@`, `snd@`: one whole-type
                // annotation instead of the former's components. Each rule is the
                // component rule with the premise `ty_check(component, level)`
                // replaced by "whnf `T` and read the component off the former",
                // and — for the three intros — the *un-reduced* `T` returned as
                // the synthesized type, which is what keeps every consumer lazy
                // in δ.
                //
                // The layer guard is the design's §2.3 and is what leaves the
                // code grammar and all 56 recursor branches alone: these forms do
                // not exist at layers c and v, so `code_eq` never meets one and
                // `rec.rs` needs no branch. `not_var_layer` would let layer c
                // through, so the guard is `computes()`.
                //
                // **The annotation is viewed in the value domain**, always —
                // design §3.4's `view_v`, which is the rule of §3.3 read from
                // the other side: the rewriter never runs on a type that came
                // through an `@` annotation. The head and the levels are read
                // out of a value and the value is dropped; the component types
                // are never spelled at all, they are `ITy::Sel` descriptions,
                // and spelling one is `Tc::materialize` and is counted. Under
                // the eager mode (§3.6) this is the rewriter again and the
                // components come back as syntax, which is what the differential
                // test holds this against.
                Term::PairAt { ty, fst, snd } => {
                    self.computing_layer(env)?;
                    let level = self.ty_infer(env, ty)?;
                    let (ity, form) = self.view_at(env, ty)?;
                    let TyForm::Sigma { fst_level, snd_level, fst: fst_c, snd: snd_c } = form
                    else {
                        return Err(TypeError::HeadMismatch);
                    };
                    self.tm_check(env, fst, fst_c.as_ref(), &fst_level)?;
                    let snd_at = snd_c.at(&env.gamma, Rc::clone(fst));
                    self.tm_check(env, snd, snd_at.as_ref(), &snd_level)?;
                    crate::stats::intro_at_nodes(1);
                    Ok((ity, level))
                }
                Term::InlAt { ty, val } | Term::InrAt { ty, val } => {
                    self.computing_layer(env)?;
                    let level = self.ty_infer(env, ty)?;
                    let (ity, form) = self.view_at(env, ty)?;
                    let TyForm::Sum { lhs_level, rhs_level, lhs, rhs } = form else {
                        return Err(TypeError::HeadMismatch);
                    };
                    let (summand, summand_level) = if matches!(t, Term::InrAt { .. }) {
                        (rhs, rhs_level)
                    } else {
                        (lhs, lhs_level)
                    };
                    self.tm_check(env, val, summand.as_ref(), &summand_level)?;
                    crate::stats::intro_at_nodes(1);
                    Ok((ity, level))
                }
                // `fst@(T; p) : S` — note the scrutinee is checked against `T`
                // itself, not against the Σ: an argument that is a `pair@` then
                // converts its own un-reduced annotation against this one, which
                // is a head comparison and not a walk of two reducts.
                Term::FstAt { ty, pair } => {
                    self.computing_layer(env)?;
                    // `ty_infer` first in all five rules: the view is untyped and
                    // must not be handed an annotation nothing has checked.
                    let level = self.ty_infer(env, ty)?;
                    let (ity, form) = self.view_at(env, ty)?;
                    let TyForm::Sigma { fst_level, fst: fst_c, .. } = form else {
                        return Err(TypeError::HeadMismatch);
                    };
                    self.tm_check(env, pair, ity.as_ref(), &level)?;
                    crate::stats::intro_at_nodes(1);
                    Ok((fst_c, fst_level))
                }
                // `snd@(T; p) : U[fst@(T;p)/x]` — the substituted term is the
                // checked spelling again, so the inferred type stays source-shaped
                // even though `U` itself came out of the whnf.
                Term::SndAt { ty, pair } => {
                    self.computing_layer(env)?;
                    let level = self.ty_infer(env, ty)?;
                    let (ity, form) = self.view_at(env, ty)?;
                    let TyForm::Sigma { snd_level, snd: snd_c, .. } = form else {
                        return Err(TypeError::HeadMismatch);
                    };
                    self.tm_check(env, pair, ity.as_ref(), &level)?;
                    let fst_p = Term::FstAt { ty: Rc::clone(ty), pair: Rc::clone(pair) };
                    crate::stats::intro_at_nodes(1);
                    Ok((snd_c.at(&env.gamma, Rc::new(fst_p)), snd_level))
                }
            _ => Err(TypeError::NotInferable),
        }
    }

    fn tm_infer_inner(&self, env: &Env, t: &Term) -> R<(Type, Level)> {
        match t {
            // The two forms layer v admits.
            Term::Var(x) => {
                let Some(e) = env.gamma.entries.nth_inner(x.0) else {
                    return Err(TypeError::UnboundLocalVar(x.0));
                };
                Ok((e.ty.shift_local(x.0 + 1), e.level.clone()))
            }
            Term::GlobalTm { var, subst } => {
                let Some(binding) = lookup(&env.psi, *var) else {
                    return Err(TypeError::UnboundGlobalVar(var.0));
                };
                let GlobalBinding::Tm { ctx, layer, ty, level, .. } = binding else {
                    return Err(TypeError::WrongGlobalBinding(var.0));
                };
                // i' ∈ {v, c} is the binding invariant; i' ≤ i:
                if *layer > env.layer {
                    return Err(TypeError::LayerMismatch);
                }
                let level = level.clone();
                crate::stats::global_ref_rescopes(1);
                let sig = env.cache.sig_or_insert(*var, || Sig {
                    ctx: ctx.shift_global(var.0 + 1),
                    ty: Some(Rc::new(ty.shift_global(var.0 + 1))),
                });
                // The binding form fixes the kind at this index, so a `Tm`
                // lookup always finds the `Tm` signature.
                let Some(ty) = sig.ty.as_ref() else {
                    return Err(TypeError::WrongGlobalBinding(var.0));
                };
                self.subst_ck(env, subst, &sig.ctx)?;
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
                self.tm_check_ty(
                    env,
                    dom,
                    &Type::Ty(dom_level.clone()),
                    &Level::succ(dom_level.clone()),
                )?;
                let el = Type::El { level: dom_level.clone(), tm: Rc::clone(dom) };
                let e = env.push_entry(Rc::new(el), dom_level.clone());
                self.tm_check_ty(
                    &e,
                    cod,
                    &Type::Ty(cod_level.clone()),
                    &Level::succ(cod_level.clone()),
                )?;
                let lmax = Level::join(dom_level.clone(), cod_level.clone());
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
                self.tm_check_ty(env, ty, &Type::Ty(level.clone()), &Level::succ(level.clone()))?;
                let el = Type::El { level: level.clone(), tm: Rc::clone(ty) };
                self.tm_check_ty(env, lhs, &el, level)?;
                self.tm_check_ty(env, rhs, &el, level)?;
                Ok((Type::Ty(level.clone()), Level::succ(level.clone())))
            }
            // Encoding of Σ (extension): Σ^{l,l'}(x:s).t : Ty (l⊔l').
            Term::TmSigma { fst_level, snd_level, fst, snd } => {
                self.not_var_layer(env)?;
                self.level_wf(env, fst_level)?;
                self.level_wf(env, snd_level)?;
                self.tm_check_ty(
                    env,
                    fst,
                    &Type::Ty(fst_level.clone()),
                    &Level::succ(fst_level.clone()),
                )?;
                let el = Type::El { level: fst_level.clone(), tm: Rc::clone(fst) };
                let e = env.push_entry(Rc::new(el), fst_level.clone());
                self.tm_check_ty(
                    &e,
                    snd,
                    &Type::Ty(snd_level.clone()),
                    &Level::succ(snd_level.clone()),
                )?;
                let lmax = Level::join(fst_level.clone(), snd_level.clone());
                Ok((Type::Ty(lmax.clone()), Level::succ(lmax)))
            }
            // Encodings of Unit/Empty (extension): Unit^l, Empty^l : Ty l.
            // The code carries `l` for the same reason `TmTy` does — it is a
            // *term*, so its type must be determined by it.
            Term::TmUnit { level } | Term::TmEmpty { level } | Term::TmSEmpty { level } => {
                self.not_var_layer(env)?;
                self.level_wf(env, level)?;
                Ok((Type::Ty(level.clone()), Level::succ(level.clone())))
            }
            Term::TmSquash { level, ty } => {
                self.not_var_layer(env)?;
                self.level_wf(env, level)?;
                self.tm_check_ty(env, ty, &Type::Ty(level.clone()), &Level::succ(level.clone()))?;
                Ok((Type::Ty(level.clone()), Level::succ(level.clone())))
            }
            // Encoding of sEq (extension; docs/sprop-design.md §6): mirrors
            // TmId — sEq^l(s; t; u) : Ty l.
            Term::TmSEq { level, ty, lhs, rhs } => {
                self.not_var_layer(env)?;
                self.level_wf(env, level)?;
                self.tm_check_ty(env, ty, &Type::Ty(level.clone()), &Level::succ(level.clone()))?;
                let el = Type::El { level: level.clone(), tm: Rc::clone(ty) };
                self.tm_check_ty(env, lhs, &el, level)?;
                self.tm_check_ty(env, rhs, &el, level)?;
                Ok((Type::Ty(level.clone()), Level::succ(level.clone())))
            }
            // Encoding of the binary sum (extension): a +^{l,l'} b : Ty (l⊔l').
            Term::TmSum { lhs_level, rhs_level, lhs, rhs } => {
                self.not_var_layer(env)?;
                self.level_wf(env, lhs_level)?;
                self.level_wf(env, rhs_level)?;
                self.tm_check_ty(
                    env,
                    lhs,
                    &Type::Ty(lhs_level.clone()),
                    &Level::succ(lhs_level.clone()),
                )?;
                self.tm_check_ty(
                    env,
                    rhs,
                    &Type::Ty(rhs_level.clone()),
                    &Level::succ(rhs_level.clone()),
                )?;
                let lmax = Level::join(lhs_level.clone(), rhs_level.clone());
                Ok((Type::Ty(lmax.clone()), Level::succ(lmax)))
            }
            // Encoding of W (extension): W^{l,l'}(x:s).t : Ty (l⊔l').
            Term::TmW { shape_level, pos_level, shape, pos } => {
                self.not_var_layer(env)?;
                self.level_wf(env, shape_level)?;
                self.level_wf(env, pos_level)?;
                self.tm_check_ty(
                    env,
                    shape,
                    &Type::Ty(shape_level.clone()),
                    &Level::succ(shape_level.clone()),
                )?;
                let el = Type::El { level: shape_level.clone(), tm: Rc::clone(shape) };
                let e = env.push_entry(Rc::new(el), shape_level.clone());
                self.tm_check_ty(
                    &e,
                    pos,
                    &Type::Ty(pos_level.clone()),
                    &Level::succ(pos_level.clone()),
                )?;
                let lmax = Level::join(shape_level.clone(), pos_level.clone());
                Ok((Type::Ty(lmax.clone()), Level::succ(lmax)))
            }
            // Encoding of Vec (extension; docs/wf-former-design.md §6):
            // Vec^l(s; k) : Ty l ⟸ s : Ty l, k : Nat. The length is a term
            // of the ambient scope, so it binds nothing.
            Term::TmVec { level, elem, len } => {
                self.not_var_layer(env)?;
                self.level_wf(env, level)?;
                self.tm_check_ty(env, elem, &Type::Ty(level.clone()), &Level::succ(level.clone()))?;
                self.tm_check_ty(env, len, &Type::Nat, &Level::Zero)?;
                Ok((Type::Ty(level.clone()), Level::succ(level.clone())))
            }
            // Encoding of Fin (extension; §6): Fin(k) : Ty 0 ⟸ k : Nat.
            Term::TmFin { len } => {
                self.not_var_layer(env)?;
                self.tm_check_ty(env, len, &Type::Nat, &Level::Zero)?;
                Ok((Type::Ty(Level::Zero), Level::constant(1)))
            }
            // Encoding of Wf (extension; §6): Wf^l(x:s). n : Ty l ⟸
            // s : Ty l, (Γ, x : El^l s) ⊢ n : Nat. As with the type former,
            // the arity is a term, so it contributes no level.
            Term::TmWf { level, shape, arity } => {
                self.not_var_layer(env)?;
                self.level_wf(env, level)?;
                self.tm_check_ty(
                    env,
                    shape,
                    &Type::Ty(level.clone()),
                    &Level::succ(level.clone()),
                )?;
                let el = Type::El { level: level.clone(), tm: Rc::clone(shape) };
                let e = env.push_entry(Rc::new(el), level.clone());
                self.tm_check_ty(&e, arity, &Type::Nat, &Level::Zero)?;
                Ok((Type::Ty(level.clone()), Level::succ(level.clone())))
            }
            Term::Zero => {
                self.not_var_layer(env)?;
                Ok((Type::Nat, Level::Zero))
            }
            Term::NatLit(_) => {
                self.not_var_layer(env)?;
                Ok((Type::Nat, Level::Zero))
            }
            Term::Succ(n) => {
                self.not_var_layer(env)?;
                self.tm_check_ty(env, n, &Type::Nat, &Level::Zero)?;
                Ok((Type::Nat, Level::Zero))
            }
            Term::ElimNat { level, motive, base, step, scrut } => {
                self.not_var_layer(env)?;
                self.level_wf(env, level)?;
                let e_x = env.push_entry(Rc::new(Type::Nat), Level::Zero);
                self.ty_check(&e_x, motive, level)?;
                let base_ty =
                    motive.apply_local(&LocalSubst::id(&env.gamma).extended(Rc::new(Term::Zero)));
                self.tm_check_ty(env, base, &base_ty, level)?;
                // M[su x/x] scoped in (Γ, x : Nat, y : M).
                let su_x = Term::Succ(Rc::new(Term::Var(LocalVar(1))));
                let step_ty = motive.apply_local(
                    &LocalSubst::id(&env.gamma).shift_local(2).extended(Rc::new(su_x)),
                );
                let e_xy = e_x.push_entry(Rc::clone(motive), level.clone());
                self.tm_check_ty(&e_xy, step, &step_ty, level)?;
                self.tm_check_ty(env, scrut, &Type::Nat, &Level::Zero)?;
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
                self.tm_check_rc(env, tm, ty, level)?;
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
                self.tm_check_rc(env, lhs, ty, ty_level)?;
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
                self.tm_check_ty(env, case, &case_ty, motive_level)?;
                self.tm_check_rc(env, rhs, ty, ty_level)?;
                let id_ty = Type::Id {
                    level: ty_level.clone(),
                    ty: Rc::clone(ty),
                    lhs: Rc::clone(lhs),
                    rhs: Rc::clone(rhs),
                };
                self.tm_check_ty(env, proof, &id_ty, ty_level)?;
                Ok((
                    motive.apply_local(
                        &LocalSubst::id(&env.gamma)
                            .extended(Rc::clone(rhs))
                            .extended(Rc::clone(proof)),
                    ),
                    motive_level.clone(),
                ))
            }

            // -- strict equality (extension; docs/sprop-design.md §3–4) -----
            // srefl^l(I; a) : sEq^l(I; a; a) @ l.
            Term::SRefl { level, ty, tm } => {
                self.not_var_layer(env)?;
                self.level_wf(env, level)?;
                self.ty_check(env, ty, level)?;
                self.tm_check_rc(env, tm, ty, level)?;
                Ok((
                    Type::SEq {
                        level: level.clone(),
                        ty: Rc::clone(ty),
                        lhs: Rc::clone(tm),
                        rhs: Rc::clone(tm),
                    },
                    level.clone(),
                ))
            }
            Term::Squash { level, ty, tm } => {
                self.not_var_layer(env)?;
                self.level_wf(env, level)?;
                self.ty_check(env, ty, level)?;
                self.tm_check_rc(env, tm, ty, level)?;
                Ok((
                    Type::Squash { level: level.clone(), ty: Rc::clone(ty) },
                    level.clone(),
                ))
            }
            // transp^{l,l'}(I; x.P; a; b; e; t) : P[b/x] @ l'. The motive
            // binds one local (x : I) — J's non-dependent cousin; no motive
            // over the proof exists or is needed (proofs are irrelevant, so
            // transp + the conv.rs irrelevance arm derive sJ).
            Term::Transp { ty_level, motive_level, ty, motive, lhs, rhs, proof, tm } => {
                self.not_var_layer(env)?;
                self.level_wf(env, ty_level)?;
                self.level_wf(env, motive_level)?;
                self.ty_check(env, ty, ty_level)?;
                self.tm_check_rc(env, lhs, ty, ty_level)?;
                self.tm_check_rc(env, rhs, ty, ty_level)?;
                let e_x = env.push_entry(Rc::clone(ty), ty_level.clone());
                self.ty_check(&e_x, motive, motive_level)?;
                let seq_ty = Type::SEq {
                    level: ty_level.clone(),
                    ty: Rc::clone(ty),
                    lhs: Rc::clone(lhs),
                    rhs: Rc::clone(rhs),
                };
                self.tm_check_ty(env, proof, &seq_ty, ty_level)?;
                let tm_ty = motive
                    .apply_local(&LocalSubst::id(&env.gamma).extended(Rc::clone(lhs)));
                self.tm_check_ty(env, tm, &tm_ty, motive_level)?;
                Ok((
                    motive.apply_local(&LocalSubst::id(&env.gamma).extended(Rc::clone(rhs))),
                    motive_level.clone(),
                ))
            }

            // elim_sEmpty^{l,l'} (x. M; t) : M[t/x] @ l — ElimEmpty's rule;
            // eliminates anywhere (the motive's level is unrestricted).
            Term::ElimSEmpty { level, scrut_level, motive, scrut } => {
                self.not_var_layer(env)?;
                self.level_wf(env, level)?;
                self.level_wf(env, scrut_level)?;
                let sempty = Type::SEmpty { level: scrut_level.clone() };
                let e_x = env.push_entry(Rc::new(sempty.clone()), scrut_level.clone());
                self.ty_check(&e_x, motive, level)?;
                self.tm_check_ty(env, scrut, &sempty, scrut_level)?;
                Ok((
                    motive.apply_local(&LocalSubst::id(&env.gamma).extended(Rc::clone(scrut))),
                    level.clone(),
                ))
            }
            Term::ElimSquash { src_level, dst_level, src_ty, motive, case, scrut } => {
                self.not_var_layer(env)?;
                self.level_wf(env, src_level)?;
                self.level_wf(env, dst_level)?;
                self.ty_check(env, src_ty, src_level)?;
                let squash_src = Type::Squash {
                    level: src_level.clone(),
                    ty: Rc::clone(src_ty),
                };
                let e_z = env.push_entry(Rc::new(squash_src.clone()), src_level.clone());
                self.ty_check(&e_z, motive, dst_level)?;

                let e_x = env.push_entry(Rc::clone(src_ty), src_level.clone());
                let witness = Rc::new(Term::Var(LocalVar(0)));
                let packed = Rc::new(Term::Squash {
                    level: src_level.clone(),
                    ty: Rc::new(src_ty.shift_local(1)),
                    tm: witness,
                });
                let case_inner = motive.apply_local(
                    &LocalSubst::id(&env.gamma).shift_local(1).extended(packed),
                );
                let case_ty = Type::Squash {
                    level: dst_level.clone(),
                    ty: Rc::new(case_inner),
                };
                self.tm_check_ty(&e_x, case, &case_ty, dst_level)?;
                self.tm_check_ty(env, scrut, &squash_src, src_level)?;
                let result_inner = motive.apply_local(
                    &LocalSubst::id(&env.gamma).extended(Rc::clone(scrut)),
                );
                Ok((
                    Type::Squash { level: dst_level.clone(), ty: Rc::new(result_inner) },
                    dst_level.clone(),
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
                self.tm_check_rc(env, fst, fst_ty, fst_level)?;
                // b : T[a/x].
                let snd_at = snd_ty
                    .apply_local(&LocalSubst::id(&env.gamma).extended(Rc::clone(fst)));
                self.tm_check_ty(env, snd, &snd_at, snd_level)?;
                Ok((
                    Type::Sigma {
                        fst_level: fst_level.clone(),
                        snd_level: snd_level.clone(),
                        fst: Rc::clone(fst_ty),
                        snd: Rc::clone(snd_ty),
                    },
                    Level::join(fst_level.clone(), snd_level.clone()),
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
                self.tm_check_ty(
                    env,
                    pair,
                    &sigma,
                    &Level::join(fst_level.clone(), snd_level.clone()),
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
                self.tm_check_ty(
                    env,
                    pair,
                    &sigma,
                    &Level::join(fst_level.clone(), snd_level.clone()),
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
            // ⟨⟩^l : Unit^l @ l.
            //
            // The level annotation is load-bearing, not decoration: without
            // it `⟨⟩` inhabits `Unit^l` for every `l`, i.e. a *term* with many
            // types, which ch. 04 §Non-cumulativity says the code eliminator
            // cannot survive (`docs/unit-empty-level-indexing.md` §2.2).
            Term::Triv { level } => {
                self.not_var_layer(env)?;
                self.level_wf(env, level)?;
                Ok((Type::Unit { level: level.clone() }, level.clone()))
            }
            // elim_Empty^{l,l'} (x. M; t) : M[t/x] @ l, scrutinee at Empty^{l'}.
            Term::ElimEmpty { level, scrut_level, motive, scrut } => {
                self.not_var_layer(env)?;
                self.level_wf(env, level)?;
                self.level_wf(env, scrut_level)?;
                let empty = Type::Empty { level: scrut_level.clone() };
                let e_x = env.push_entry(Rc::new(empty.clone()), scrut_level.clone());
                self.ty_check(&e_x, motive, level)?;
                self.tm_check_ty(env, scrut, &empty, scrut_level)?;
                Ok((
                    motive.apply_local(&LocalSubst::id(&env.gamma).extended(Rc::clone(scrut))),
                    level.clone(),
                ))
            }

            // -- binary sums (extension beyond ch. 04) ----------------------
            // inl^{l,l'}(A; B; a) : A +^{l,l'} B @ l⊔l'.
            Term::Inl { lhs_level, rhs_level, lhs, rhs, val } => {
                self.not_var_layer(env)?;
                self.level_wf(env, lhs_level)?;
                self.level_wf(env, rhs_level)?;
                self.ty_check(env, lhs, lhs_level)?;
                self.ty_check(env, rhs, rhs_level)?;
                self.tm_check_rc(env, val, lhs, lhs_level)?;
                Ok((
                    Type::Sum {
                        lhs_level: lhs_level.clone(),
                        rhs_level: rhs_level.clone(),
                        lhs: Rc::clone(lhs),
                        rhs: Rc::clone(rhs),
                    },
                    Level::join(lhs_level.clone(), rhs_level.clone()),
                ))
            }
            // inr^{l,l'}(A; B; b) : A +^{l,l'} B @ l⊔l'.
            Term::Inr { lhs_level, rhs_level, lhs, rhs, val } => {
                self.not_var_layer(env)?;
                self.level_wf(env, lhs_level)?;
                self.level_wf(env, rhs_level)?;
                self.ty_check(env, lhs, lhs_level)?;
                self.ty_check(env, rhs, rhs_level)?;
                self.tm_check_rc(env, val, rhs, rhs_level)?;
                Ok((
                    Type::Sum {
                        lhs_level: lhs_level.clone(),
                        rhs_level: rhs_level.clone(),
                        lhs: Rc::clone(lhs),
                        rhs: Rc::clone(rhs),
                    },
                    Level::join(lhs_level.clone(), rhs_level.clone()),
                ))
            }
            // case^{l,l',l''}(z. M; A; B; x. c_l; y. c_r; t) : M[t/z] @ l''.
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
                self.not_var_layer(env)?;
                self.level_wf(env, lhs_level)?;
                self.level_wf(env, rhs_level)?;
                self.level_wf(env, motive_level)?;
                self.ty_check(env, lhs, lhs_level)?;
                self.ty_check(env, rhs, rhs_level)?;
                let lmax = Level::join(lhs_level.clone(), rhs_level.clone());
                let sum = Type::Sum {
                    lhs_level: lhs_level.clone(),
                    rhs_level: rhs_level.clone(),
                    lhs: Rc::clone(lhs),
                    rhs: Rc::clone(rhs),
                };
                // M scoped in (Γ, z : A + B).
                let e_z = env.push_entry(Rc::new(sum.clone()), lmax.clone());
                self.ty_check(&e_z, motive, motive_level)?;
                // c_l : M[inl x/z] scoped in (Γ, x : A).
                let e_x = env.push_entry(Rc::clone(lhs), lhs_level.clone());
                let inl_x = Term::Inl {
                    lhs_level: lhs_level.clone(),
                    rhs_level: rhs_level.clone(),
                    lhs: Rc::new(lhs.shift_local(1)),
                    rhs: Rc::new(rhs.shift_local(1)),
                    val: Rc::new(Term::Var(LocalVar(0))),
                };
                let left_ty = motive.apply_local(
                    &LocalSubst::id(&env.gamma).shift_local(1).extended(Rc::new(inl_x)),
                );
                self.tm_check_ty(&e_x, case_l, &left_ty, motive_level)?;
                // c_r : M[inr y/z] scoped in (Γ, y : B).
                let e_y = env.push_entry(Rc::clone(rhs), rhs_level.clone());
                let inr_y = Term::Inr {
                    lhs_level: lhs_level.clone(),
                    rhs_level: rhs_level.clone(),
                    lhs: Rc::new(lhs.shift_local(1)),
                    rhs: Rc::new(rhs.shift_local(1)),
                    val: Rc::new(Term::Var(LocalVar(0))),
                };
                let right_ty = motive.apply_local(
                    &LocalSubst::id(&env.gamma).shift_local(1).extended(Rc::new(inr_y)),
                );
                self.tm_check_ty(&e_y, case_r, &right_ty, motive_level)?;
                self.tm_check_ty(env, scrut, &sum, &lmax)?;
                Ok((
                    motive.apply_local(&LocalSubst::id(&env.gamma).extended(Rc::clone(scrut))),
                    motive_level.clone(),
                ))
            }

            // -- well-founded trees (extension beyond ch. 04) ---------------
            // sup^{l,l'}(x:S.T; a; f) : W^{l,l'}(x:S).T @ l⊔l' with a : S and
            // f : Π^{l',l⊔l'}(y : T[a/x]). W.
            Term::Sup { shape_level, pos_level, shape_ty, pos_ty, label, children } => {
                self.not_var_layer(env)?;
                self.level_wf(env, shape_level)?;
                self.level_wf(env, pos_level)?;
                self.ty_check(env, shape_ty, shape_level)?;
                let e = env.push_entry(Rc::clone(shape_ty), shape_level.clone());
                self.ty_check(&e, pos_ty, pos_level)?;
                self.tm_check_rc(env, label, shape_ty, shape_level)?;
                let lmax = Level::join(shape_level.clone(), pos_level.clone());
                let w = Type::W {
                    shape_level: shape_level.clone(),
                    pos_level: pos_level.clone(),
                    shape: Rc::clone(shape_ty),
                    pos: Rc::clone(pos_ty),
                };
                // f : Π(y : T[a/x]). W (W weakened under y).
                let pos_at = pos_ty
                    .apply_local(&LocalSubst::id(&env.gamma).extended(Rc::clone(label)));
                let f_ty = Type::Pi {
                    dom_level: pos_level.clone(),
                    cod_level: lmax.clone(),
                    dom: Rc::new(pos_at),
                    cod: Rc::new(w.shift_local(1)),
                };
                self.tm_check_ty(
                    env,
                    children,
                    &f_ty,
                    &Level::join(pos_level.clone(), lmax.clone()),
                )?;
                Ok((w, lmax))
            }
            // elim_W^{l,l',l''}(x:S.T; z. M; a f ih. s; t) : M[t/z] @ l''.
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
                self.not_var_layer(env)?;
                self.level_wf(env, shape_level)?;
                self.level_wf(env, pos_level)?;
                self.level_wf(env, motive_level)?;
                self.ty_check(env, shape, shape_level)?;
                let e_x = env.push_entry(Rc::clone(shape), shape_level.clone());
                self.ty_check(&e_x, pos, pos_level)?;
                let lmax = Level::join(shape_level.clone(), pos_level.clone());
                let w = Type::W {
                    shape_level: shape_level.clone(),
                    pos_level: pos_level.clone(),
                    shape: Rc::clone(shape),
                    pos: Rc::clone(pos),
                };
                // M scoped in (Γ, z : W).
                let e_z = env.push_entry(Rc::new(w.clone()), lmax.clone());
                self.ty_check(&e_z, motive, motive_level)?;
                // Step scoped in (Γ, a : S, f : Π(y:T[a/x]). W,
                // ih : Π(y:T[a/x]). M[f y/z]). In (Γ, a), T[a/x] is `pos`
                // itself (a sits exactly where the binder x was).
                let e_a = env.push_entry(Rc::clone(shape), shape_level.clone());
                let f_ty = Type::Pi {
                    dom_level: pos_level.clone(),
                    cod_level: lmax.clone(),
                    dom: Rc::clone(pos),
                    cod: Rc::new(w.shift_local(2)),
                };
                let f_level = Level::join(pos_level.clone(), lmax.clone());
                let e_af = e_a.push_entry(Rc::new(f_ty), f_level);
                // f y in (Γ, a, f, y : T[a/x]): f = Var 1, y = Var 0.
                let f_y = Term::App {
                    fun: Rc::new(Term::Var(LocalVar(1))),
                    dom_level: pos_level.clone(),
                    cod_level: lmax.clone(),
                    dom: Rc::new(pos.shift_local(2)),
                    cod: Rc::new(w.shift_local(4)),
                    arg: Rc::new(Term::Var(LocalVar(0))),
                };
                let ih_cod = motive.apply_local(
                    &LocalSubst::id(&env.gamma).shift_local(3).extended(Rc::new(f_y)),
                );
                let ih_ty = Type::Pi {
                    dom_level: pos_level.clone(),
                    cod_level: motive_level.clone(),
                    dom: Rc::new(pos.shift_local(1)),
                    cod: Rc::new(ih_cod),
                };
                let ih_level = Level::join(pos_level.clone(), motive_level.clone());
                let e_step = e_af.push_entry(Rc::new(ih_ty), ih_level);
                // s : M[sup(a, f)/z] with sup built in (Γ, a, f), then
                // weakened past ih.
                let Type::W { shape: s2, pos: p2, .. } = w.shift_local(2) else {
                    unreachable!()
                };
                let sup_af = Term::Sup {
                    shape_level: shape_level.clone(),
                    pos_level: pos_level.clone(),
                    shape_ty: s2,
                    pos_ty: p2,
                    label: Rc::new(Term::Var(LocalVar(1))),
                    children: Rc::new(Term::Var(LocalVar(0))),
                };
                let step_ty = motive.apply_local(
                    &LocalSubst::id(&env.gamma)
                        .shift_local(3)
                        .extended(Rc::new(sup_af.shift_local(1))),
                );
                self.tm_check_ty(&e_step, step, &step_ty, motive_level)?;
                self.tm_check_ty(env, scrut, &w, &lmax)?;
                Ok((
                    motive.apply_local(&LocalSubst::id(&env.gamma).extended(Rc::clone(scrut))),
                    motive_level.clone(),
                ))
            }

            // sup_f^l(x:S. n; a; cs) : Wf^l(x:S). n @ l, with
            // cs : Vec^l(Wf; n[a/x]) — children as a tuple.
            Term::Supf { level, shape, arity, label, children } => {
                self.not_var_layer(env)?;
                self.level_wf(env, level)?;
                self.ty_check(env, shape, level)?;
                let e_x = env.push_entry(Rc::clone(shape), level.clone());
                self.tm_check_ty(&e_x, arity, &Type::Nat, &Level::Zero)?;
                self.tm_check_rc(env, label, shape, level)?;
                let wf = Type::Wf {
                    level: level.clone(),
                    shape: Rc::clone(shape),
                    arity: Rc::clone(arity),
                };
                let arity_at =
                    arity.apply_local(&LocalSubst::id(&env.gamma).extended(Rc::clone(label)));
                let cs_ty = Type::Vec {
                    level: level.clone(),
                    elem: Rc::new(wf.clone()),
                    len: Rc::new(arity_at),
                };
                self.tm_check_ty(env, children, &cs_ty, level)?;
                Ok((wf, level.clone()))
            }
            // elim_Wf^{l,l'}(x:S. n; z. M; a cs ih. s; t) : M[t/z] @ l'.
            // The step telescope (children tuple, `Fin`-indexed ih, arm
            // obligation at the constructor form) is built by
            // `wf_step_telescope`, shared verbatim with conv.rs.
            Term::ElimWf { level, motive_level, shape, arity, motive, step, scrut } => {
                self.not_var_layer(env)?;
                self.level_wf(env, level)?;
                self.level_wf(env, motive_level)?;
                self.ty_check(env, shape, level)?;
                let e_x = env.push_entry(Rc::clone(shape), level.clone());
                self.tm_check_ty(&e_x, arity, &Type::Nat, &Level::Zero)?;
                let wf = Type::Wf {
                    level: level.clone(),
                    shape: Rc::clone(shape),
                    arity: Rc::clone(arity),
                };
                // M scoped in (Γ, z : Wf).
                let e_z = env.push_entry(Rc::new(wf.clone()), level.clone());
                self.ty_check(&e_z, motive, motive_level)?;
                let (cs_ty, ih_ty, step_ty) = wf_step_telescope(
                    &env.gamma,
                    level,
                    motive_level,
                    shape,
                    arity,
                    motive,
                );
                let e_a = env.push_entry(Rc::clone(shape), level.clone());
                let e_cs = e_a.push_entry(Rc::new(cs_ty), level.clone());
                let e_step = e_cs.push_entry(Rc::new(ih_ty), motive_level.clone());
                self.tm_check_ty(&e_step, step, &step_ty, motive_level)?;
                self.tm_check_ty(env, scrut, &wf, level)?;
                Ok((
                    motive.apply_local(&LocalSubst::id(&env.gamma).extended(Rc::clone(scrut))),
                    motive_level.clone(),
                ))
            }

            // -- dependent functions ----------------------------------------
            Term::Lam { dom_level, cod_level, dom, body } => {
                self.not_var_layer(env)?;
                self.level_wf(env, dom_level)?;
                self.level_wf(env, cod_level)?;
                self.ty_check(env, dom, dom_level)?;
                let e = env.push_entry(Rc::clone(dom), dom_level.clone());
                // §3.5 again — the λ that binds a *term*. The design names
                // the three layer-m arms; this one has the same shape and
                // the same reason, and leaving it out would be the one
                // incomplete arm.
                let (cod, cl) = self.tm_infer_syn(&e, body)?;
                self.lev_eq(cod_level, &cl)?;
                Ok((
                    Type::Pi {
                        dom_level: dom_level.clone(),
                        cod_level: cod_level.clone(),
                        dom: Rc::clone(dom),
                        cod,
                    },
                    Level::join(dom_level.clone(), cod_level.clone()),
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
                self.tm_check_ty(
                    env,
                    fun,
                    &pi,
                    &Level::join(dom_level.clone(), cod_level.clone()),
                )?;
                self.tm_check_rc(env, arg, dom, dom_level)?;
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
                // §3.5: the body's inferred type has to go *inside* a
                // syntactic former, so a selection is spelled here. On every
                // declaration that exists today this is a `Syn` and
                // `materialize` is `Rc::clone`; the shape that is not is a
                // layer-m metaprogram whose body infers a tower component,
                // and it is complete rather than fast, which is the right
                // way round for a trusted checker.
                let (ty, lt) = self.tm_infer_syn(&e, body)?;
                self.lev_eq(level, &lt)?;
                Ok((
                    Type::UPi { num_vars: *num_vars, level: level.clone(), body: ty },
                    Level::Omega,
                ))
            }
            Term::UApp { fun, levels } => {
                self.meta_layer(env)?;
                let (fun_ty, fl) = self.tm_infer(env, fun)?;
                self.lev_eq(&fl, &Level::Omega)?;
                let Type::UPi { num_vars, level, body } = self.whnf(env, fun_ty.as_ref())? else {
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
                let (ty, lt) = self.tm_infer_syn(&e, body)?;
                self.lev_eq(level, &lt)?;
                Ok((Type::CtxPi { level: level.clone(), body: ty }, level.clone()))
            }
            Term::CtxApp { fun, ctx } => {
                self.meta_layer(env)?;
                let (fun_ty, _) = self.tm_infer(env, fun)?;
                let Type::CtxPi { level, body } = self.whnf(env, fun_ty.as_ref())? else {
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
                let (ty, lt) = self.tm_infer_syn(&e, body)?;
                self.lev_eq(body_level, &lt)?;
                Ok((
                    Type::TyPi {
                        ctx: ctx.clone(),
                        arg_level: arg_level.clone(),
                        body_level: body_level.clone(),
                        body: ty,
                    },
                    body_level.clone(),
                ))
            }
            Term::TyApp { fun, arg } => {
                self.meta_layer(env)?;
                let (fun_ty, _) = self.tm_infer(env, fun)?;
                let Type::TyPi { ctx, arg_level, body_level, body } =
                    self.whnf(env, fun_ty.as_ref())?
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

            // The checked spellings: [`Tc::tm_infer`] routes them to
            // [`Tc::tm_infer_at`] before this match is reached, because
            // their inferred type is an [`ITy`] and every arm here produces
            // syntax.
            Term::PairAt { .. }
            | Term::InlAt { .. }
            | Term::InrAt { .. }
            | Term::FstAt { .. }
            | Term::SndAt { .. } => Err(TypeError::NotInferable),

            Term::LetBoxTy { motive_level, code_level, ctx, motive, body, scrut } => {
                self.meta_layer(env)?;
                self.level_wf(env, motive_level)?;
                self.level_wf(env, code_level)?;
                self.ctx_wf(env, Layer::Prog, ctx)?;
                let code_ty =
                    Type::CodeTy { ctx: ctx.clone(), level: code_level.clone() };
                self.tm_check_ty(env, scrut, &code_ty, &Level::Zero)?;
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
                self.tm_check_ty(&e_u, body, &body_ty, motive_level)?;
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
                self.tm_check_ty(env, scrut, &code_ty, &Level::Zero)?;
                let e_x = env.push_entry(Rc::new(code_ty), Level::Zero);
                self.ty_check(&e_x, motive, motive_level)?;
                // Body under Ψ, u : Trm_c(Δ ⊢ T @ l) at M[box u^id/x_t].
                let e_u = env.push_global(GlobalBinding::Tm {
                    ctx: ctx.clone(),
                    layer: Layer::Code,
                    ty: Rc::clone(ty),
                    level: code_level.clone(),
                    body: None,
                });
                let box_u = Term::BoxTm(Rc::new(gtm(0, &ctx.shift_global(1))));
                let body_ty = motive
                    .shift_global(1)
                    .apply_local(&LocalSubst::id(&e_u.gamma).extended(Rc::new(box_u)));
                self.tm_check_ty(&e_u, body, &body_ty, motive_level)?;
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
                self.tm_check_ty(env, scrut, &code_ty, &Level::Zero)?;
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
                self.tm_check_ty(env, scrut, &code_ty, &Level::Zero)?;
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
    /// scopes, and all 56 branches at their instantiated motive types.
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
            self.tm_check_rc(&e, b, &spec.ty, &spec.level)?;
        }
        Ok(())
    }
}

/// A cheap identity hint for partitioning the conversion memo. A mismatch is
/// allowed to miss a structurally equal entry; a match is never trusted until
/// the complete judgment has been compared. Cloning Heather syntax preserves
/// these child `Rc`s, which distinguishes the mostly-fresh types produced by
/// inference without recursively hashing them.
/// The variant name of a term, for the sampler's site column.
#[cfg(feature = "value-metrics")]
fn term_head(t: &Term) -> &'static str {
    match t {
        Term::Var(..) => "Var",
        Term::TmNat => "TmNat",
        Term::TmPi { .. } => "TmPi",
        Term::TmTy(..) => "TmTy",
        Term::TmId { .. } => "TmId",
        Term::TmSEq { .. } => "TmSEq",
        Term::TmSEmpty { .. } => "TmSEmpty",
        Term::TmSquash { .. } => "TmSquash",
        Term::TmSigma { .. } => "TmSigma",
        Term::TmUnit { .. } => "TmUnit",
        Term::TmEmpty { .. } => "TmEmpty",
        Term::TmSum { .. } => "TmSum",
        Term::TmW { .. } => "TmW",
        Term::TmVec { .. } => "TmVec",
        Term::TmFin { .. } => "TmFin",
        Term::TmWf { .. } => "TmWf",
        Term::Zero => "Zero",
        Term::NatLit(..) => "NatLit",
        Term::Succ(..) => "Succ",
        Term::ElimNat { .. } => "ElimNat",
        Term::Refl { .. } => "Refl",
        Term::J { .. } => "J",
        Term::SRefl { .. } => "SRefl",
        Term::Squash { .. } => "Squash",
        Term::Transp { .. } => "Transp",
        Term::ElimSEmpty { .. } => "ElimSEmpty",
        Term::ElimSquash { .. } => "ElimSquash",
        Term::Pair { .. } => "Pair",
        Term::Fst { .. } => "Fst",
        Term::Snd { .. } => "Snd",
        Term::Triv { .. } => "Triv",
        Term::ElimEmpty { .. } => "ElimEmpty",
        Term::Inl { .. } => "Inl",
        Term::Inr { .. } => "Inr",
        Term::Case { .. } => "Case",
        Term::Sup { .. } => "Sup",
        Term::ElimW { .. } => "ElimW",
        Term::Supf { .. } => "Supf",
        Term::ElimWf { .. } => "ElimWf",
        Term::Lam { .. } => "Lam",
        Term::App { .. } => "App",
        Term::ULam { .. } => "ULam",
        Term::UApp { .. } => "UApp",
        Term::GlobalTm { .. } => "GlobalTm",
        Term::CtxLam { .. } => "CtxLam",
        Term::CtxApp { .. } => "CtxApp",
        Term::TyLam { .. } => "TyLam",
        Term::TyApp { .. } => "TyApp",
        Term::BoxTy(..) => "BoxTy",
        Term::BoxTm(..) => "BoxTm",
        Term::LetBoxTy { .. } => "LetBoxTy",
        Term::LetBoxTm { .. } => "LetBoxTm",
        // The checked spellings (docs/intro-by-type-design.md). Stage 1a
        // added the `Term` variants and missed this match; the sampler is
        // behind `value-metrics`, which nothing in `scripts/test` builds, so
        // nothing said so.
        Term::PairAt { .. } => "PairAt",
        Term::InlAt { .. } => "InlAt",
        Term::InrAt { .. } => "InrAt",
        Term::FstAt { .. } => "FstAt",
        Term::SndAt { .. } => "SndAt",
        Term::ElimCodeTy { .. } => "ElimCodeTy",
        Term::ElimCodeTm { .. } => "ElimCodeTm",
    }
}

/// The head of a type for the miss sampler's buckets. `El` is split three
/// ways because that is the distinction the buckets exist to make: a
/// **named** code (`El (u^δ)`), a code **literal** (`El ⌜…⌝`, the lazy
/// decode's spelling), and anything else.
#[cfg(feature = "value-metrics")]
fn type_head(ty: &Type) -> &'static str {
    match ty {
        Type::Nat => "Nat",
        Type::Pi { .. } => "Pi",
        Type::Ty(_) => "Ty",
        Type::UPi { .. } => "UPi",
        Type::El { tm, .. } => match &**tm {
            Term::GlobalTm { .. } => "El^δ",
            Term::TmNat
            | Term::TmTy(_)
            | Term::TmPi { .. }
            | Term::TmId { .. }
            | Term::TmSigma { .. }
            | Term::TmUnit { .. }
            | Term::TmEmpty { .. }
            | Term::TmSum { .. }
            | Term::TmW { .. }
            | Term::TmVec { .. }
            | Term::TmFin { .. }
            | Term::TmWf { .. }
            | Term::TmSEq { .. } => "El⌜⌝",
            _ => "El(?)",
        },
        Type::Id { .. } => "Id",
        Type::SEq { .. } => "SEq",
        Type::SEmpty { .. } => "SEmpty",
        Type::Squash { .. } => "Squash",
        Type::Sigma { .. } => "Sigma",
        Type::Unit { .. } => "Unit",
        Type::Empty { .. } => "Empty",
        Type::Sum { .. } => "Sum",
        Type::W { .. } => "W",
        Type::Vec { .. } => "Vec",
        Type::Fin { .. } => "Fin",
        Type::Wf { .. } => "Wf",
        _ => "other",
    }
}

/// The exact renderings of both sides around their first difference, with
/// each side's total rendered length — enough to see *which* spelling of a
/// type met which, without printing either whole. Rendering is capped so a
/// pathological type cannot turn the sampler into the OOM it is diagnosing.
#[cfg(feature = "value-metrics")]
fn first_difference_excerpt(expected: &Type, inferred: &Type) -> String {
    use std::fmt::Write as _;
    const CAP: usize = 8 << 20;
    const WINDOW: usize = 160;
    struct Capped(String);
    impl std::fmt::Write for Capped {
        fn write_str(&mut self, s: &str) -> std::fmt::Result {
            if self.0.len() + s.len() > CAP {
                return Err(std::fmt::Error);
            }
            self.0.push_str(s);
            Ok(())
        }
    }
    let render = |ty: &Type| {
        let mut sink = Capped(String::new());
        let capped = crate::fmt::write_exact(&mut sink, ty).is_err();
        (sink.0, capped)
    };
    let (a, a_capped) = render(expected);
    let (b, b_capped) = render(inferred);
    let diff = a
        .bytes()
        .zip(b.bytes())
        .position(|(x, y)| x != y)
        .unwrap_or(a.len().min(b.len()));
    let window = |s: &str| {
        let mut start = diff.saturating_sub(WINDOW / 4).min(s.len());
        while !s.is_char_boundary(start) {
            start -= 1;
        }
        let mut end = (diff + WINDOW).min(s.len());
        while !s.is_char_boundary(end) {
            end += 1;
        }
        s[start..end].replace('\n', " ")
    };
    let mut out = String::new();
    let _ = writeln!(
        out,
        "expected len={}{} inferred len={}{} first difference at {diff}",
        a.len(),
        if a_capped { "+" } else { "" },
        b.len(),
        if b_capped { "+" } else { "" },
    );
    let _ = writeln!(out, "expected: …{}…", window(&a));
    let _ = writeln!(out, "inferred: …{}…", window(&b));
    out
}

fn type_anchor(ty: &Type) -> TypeAnchor {
    match ty {
        Type::Pi { dom, .. } => TypeAnchor::Type(RcIdentity::new(Rc::clone(dom))),
        Type::UPi { body, .. } => TypeAnchor::Type(RcIdentity::new(Rc::clone(body))),
        Type::El { tm, .. } => TypeAnchor::Term(RcIdentity::new(Rc::clone(tm))),
        Type::Id { ty, .. } | Type::SEq { ty, .. } | Type::Squash { ty, .. } => {
            TypeAnchor::Type(RcIdentity::new(Rc::clone(ty)))
        }
        Type::Sigma { fst, .. } => TypeAnchor::Type(RcIdentity::new(Rc::clone(fst))),
        Type::Sum { lhs, .. } => TypeAnchor::Type(RcIdentity::new(Rc::clone(lhs))),
        Type::W { shape, .. } | Type::Wf { shape, .. } => {
            TypeAnchor::Type(RcIdentity::new(Rc::clone(shape)))
        }
        Type::Vec { elem, .. } => TypeAnchor::Type(RcIdentity::new(Rc::clone(elem))),
        Type::Fin { len } => TypeAnchor::Term(RcIdentity::new(Rc::clone(len))),
        Type::CtxPi { body, .. } | Type::TyPi { body, .. } => {
            TypeAnchor::Type(RcIdentity::new(Rc::clone(body)))
        }
        Type::CodeTm { ty, .. } => TypeAnchor::Type(RcIdentity::new(Rc::clone(ty))),
        Type::Nat
        | Type::Ty(_)
        | Type::SEmpty { .. }
        | Type::Unit { .. }
        | Type::Empty { .. }
        | Type::GlobalTy { .. }
        | Type::CodeTy { .. } => TypeAnchor::None,
    }
}

#[cfg(test)]
mod memo_tests {
    use super::*;

    fn env(psi: GlobalCtx) -> Env {
        Env {
            psi,
            cache: Rc::new(GlobalCache::new()),
            gamma: LocalCtx::nil(),
            layer: Layer::Prog,
            univs: 0,
            #[cfg(feature = "value-metrics")]
            value_metrics: None,
        }
    }

    /// The tests below predate [`ITy`] and state their judgments in syntax;
    /// wrapping at the call is the whole adaptation.
    fn s(t: Type) -> ITy {
        ITy::Syn(Rc::new(t))
    }

    fn encoded_nat() -> Type {
        Type::El { level: Level::Zero, tm: Rc::new(Term::TmNat) }
    }

    #[test]
    fn positive_conversion_is_reused_only_in_the_same_world() {
        let tc = Tc::new(DEFAULT_FUEL);
        let first = env(GlobalCtx::default());
        let encoded = encoded_nat();
        tc.conv_ty(&first, s(encoded.clone()).as_ref(), s(Type::Nat).as_ref(), &Level::Zero).unwrap();
        assert_eq!(tc.conv_memo_entries.get(), 1);
        tc.conv_ty(&first, s(encoded.clone()).as_ref(), s(Type::Nat).as_ref(), &Level::Zero).unwrap();
        assert_eq!(tc.conv_memo_entries.get(), 1, "the exact judgment is a hit");

        let second = env(GlobalCtx::default());
        tc.conv_ty(&second, s(encoded.clone()).as_ref(), s(Type::Nat).as_ref(), &Level::Zero)
            .unwrap();
        assert_eq!(
            tc.conv_memo_entries.get(),
            2,
            "a structurally equal but separately owned Psi is not reused",
        );
    }

    #[test]
    fn failures_are_not_memoized_and_reflexivity_keeps_its_fuel_boundary() {
        let tc = Tc::new(DEFAULT_FUEL);
        let e = env(GlobalCtx::default());
        assert_eq!(
            tc.conv_ty(&e,
                s(encoded_nat()).as_ref(),
                s(Type::Unit { level: Level::Zero }).as_ref(),
                &Level::Zero,
            ),
            Err(TypeError::NotConvertible),
        );
        assert_eq!(tc.conv_memo_entries.get(), 0);

        let empty = Tc::new(0);
        assert_eq!(
            empty.conv_ty(&e, s(Type::Nat).as_ref(), s(Type::Nat).as_ref(), &Level::Zero),
            Err(TypeError::OutOfFuel),
        );
        Tc::new(1)
            .conv_ty(&e, s(Type::Nat).as_ref(), s(Type::Nat).as_ref(), &Level::Zero)
            .unwrap();
    }

    /// A `Ty 0`-coded definition whose body is `code`.
    fn code_def(code: Term) -> GlobalBinding {
        GlobalBinding::Tm {
            ctx: LocalCtx::nil(),
            layer: Layer::Code,
            ty: Rc::new(Type::Ty(Level::Zero)),
            level: Level::constant(1),
            body: Some(Rc::new(code)),
        }
    }

    fn el_of_global(v: u32) -> Type {
        Type::El {
            level: Level::Zero,
            tm: Rc::new(Term::GlobalTm {
                var: GlobalVar(v),
                subst: LocalSubst {
                    tail: SubstTail::Empty { len: 0, base: CtxBase::Nil },
                    terms: vec![],
                },
            }),
        }
    }

    /// A term *declaration* — no body, so nothing here is about δ — with the
    /// given declared context and type.
    fn decl(ctx: LocalCtx, ty: Type) -> GlobalBinding {
        GlobalBinding::Tm {
            ctx,
            layer: Layer::Var,
            ty: Rc::new(ty),
            level: Level::Zero,
            body: None,
        }
    }

    fn global_tm(v: u32) -> Term {
        Term::GlobalTm {
            var: GlobalVar(v),
            subst: LocalSubst {
                tail: SubstTail::Empty { len: 0, base: CtxBase::Nil },
                terms: vec![],
            },
        }
    }

    #[test]
    fn a_telescope_push_rebuilds_the_signature_cache() {
        // The body cache's invariant, for the other half of `Env::cache`: the
        // binding **signature** — its declared Δ and type, rescoped into the
        // ambient Ψ — that the `u^δ` rules read off every occurrence. After a
        // push, index 1 denotes a different binding with a different
        // signature, so an entry surviving the push is a wrong-type (and
        // wrong-Δ) soundness bug, not a slowdown. Conversion's half of the
        // invariant is the body test below: the two facts share one cache and
        // one rebuild, by construction.
        let tc = Tc::new(DEFAULT_FUEL);

        // The declared *type*: `Nat` at index 1 before the push, `Unit⁰` after.
        let outer = env(GlobalCtx::new(vec![
            decl(LocalCtx::nil(), Type::Nat),
            decl(LocalCtx::nil(), Type::Unit { level: Level::Zero }),
        ]));
        let u1 = global_tm(1);
        assert_eq!(tc.tm_infer_syn(&outer, &u1).map(|(t, _)| (*t).clone()), Ok(Type::Nat));
        let pushed = outer.push_global(GlobalBinding::Ctx);
        assert_eq!(
            tc.tm_infer_syn(&pushed, &u1).map(|(t, _)| (*t).clone()),
            Ok(Type::Unit { level: Level::Zero }),
            "the signature cache survived a telescope push",
        );
        // And index 2 is the outer binding again, now needing `shift_global(3)`.
        assert_eq!(tc.tm_infer_syn(&pushed, &global_tm(2)).map(|(t, _)| (*t).clone()), Ok(Type::Nat));

        // The declared *context*, the other field of the signature: `·` at
        // index 1 before the push and `(·, x : Nat)` after, so the length-zero
        // substitution above must stop being accepted.
        let mut one = LocalCtx::nil();
        one.entries.push(CtxEntry { ty: Rc::new(Type::Nat), level: Level::Zero });
        let outer = env(GlobalCtx::new(vec![
            decl(LocalCtx::nil(), Type::Nat),
            decl(one, Type::Nat),
        ]));
        assert_eq!(tc.tm_infer_syn(&outer, &u1).map(|(t, _)| (*t).clone()), Ok(Type::Nat));
        let pushed = outer.push_global(GlobalBinding::Ctx);
        assert_eq!(
            tc.tm_infer_syn(&pushed, &u1).map(|(t, _)| (*t).clone()),
            Err(TypeError::SubstMismatch),
            "the signature cache's declared context survived a telescope push",
        );
    }

    #[test]
    fn a_telescope_push_rebuilds_the_body_cache() {
        // `Env::cache` is keyed by a Ψ-index, and `push_tele` is the one
        // operation that makes those keys mean something else: after a push,
        // index 1 below denotes the *inner* definition, not the outer one. A
        // cache shared across the push would answer with the body it cached
        // before it, which is a wrong-body soundness bug and not a slowdown.
        let psi = GlobalCtx::new(vec![
            code_def(Term::TmNat),
            code_def(Term::TmUnit { level: Level::Zero }),
        ]);
        let tc = Tc::new(DEFAULT_FUEL);
        let outer = env(psi);
        // Index 1 is the outer definition, `⌜Nat⌝`; warm the cache at it.
        assert_eq!(tc.whnf_syn(&outer, &el_of_global(1)), Ok(Type::Nat));
        // One more binding, and index 1 is the inner definition, `⌜Unit⁰⌝`.
        let pushed = outer.push_global(GlobalBinding::Ctx);
        assert_eq!(
            tc.whnf_syn(&pushed, &el_of_global(1)),
            Ok(Type::Unit { level: Level::Zero }),
            "the body cache survived a telescope push",
        );
        // And index 2 is the outer one again, now needing `shift_global(3)`.
        assert_eq!(tc.whnf_syn(&pushed, &el_of_global(2)), Ok(Type::Nat));
        // Conversion agrees through its own `Env::push_tele`, which is the
        // other half of the invariant: the two must rebuild together.
        tc.conv_ty(
            &pushed,
            s(el_of_global(1)).as_ref(),
            s(Type::Unit { level: Level::Zero }).as_ref(),
            &Level::Zero,
        )
            .unwrap();
        assert_eq!(
            tc.conv_ty(
                &pushed,
                s(el_of_global(1)).as_ref(),
                s(Type::Nat).as_ref(),
                &Level::Zero,
            ),
            Err(TypeError::NotConvertible),
        );
    }
}
