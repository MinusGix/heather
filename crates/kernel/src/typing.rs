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
//! - The recursor rules check the two motives and 65 branches against the
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
//!
//! **The typing memo** (`issues/kernel-typing-memo-on-node-identity.md`).
//! A term node reachable along two paths (a `let` alias's value used twice)
//! is one allocation, and the rules would judge it once per path: a chain of
//! `k` lets, each using the last twice, is `k` nodes and `2^k` paths. So one
//! public checking gate keeps, per node *and scope*, what the node was
//! judged to be ([`Judged`]): its inferred type and level, for the
//! elimination forms (the ones checking reaches only through inference),
//! and the expected types it was checked against, for the intro forms that
//! check structurally. A later path into the same node in the same scope is
//! answered from the memo, and so is everything beneath it.
//!
//! - **The key is identity, never structure**: the node's allocation, Ψ's
//!   and Γ's identity tokens, Γ's base, the layer, `|L|` and the `box` bit
//!   ([`Scope`]). Those are everything a rule reads besides the node, so a
//!   hit is the judgment the rules would make again. Each entry holds the
//!   node and both tokens, so no address in a live key is ever reused; the
//!   memo is dropped with the checker when the gate returns.
//! - **Deterministic, so a hit may skip fuel.** Whether a lookup hits
//!   depends only on which node and scope objects the rules pass along,
//!   which the term's sharing decides, not on addresses or reference counts
//!   (a count would be perturbed by the bounds cache's keep-alives). Every
//!   eligible node gets an entry, chosen by its kind, and nothing is evicted.
//!   So `--timings` counts and `OutOfFuel` verdicts stay functions of the
//!   input, at any worker count.
//! - **Strengthened scopes** (issues/indexed-family-recursion-gate-cost.md).
//!   A node that holds no weakening tail `wk^k_g` and reads only Γ's innermost
//!   `k ≤ STRENGTHEN_MAX` entries, whose own types stay inside those `k`, is
//!   judged by those entries alone; the rules read nothing else of Γ. Its
//!   scope then names the `k` entries (types by identity, levels by value,
//!   interned in [`Tc::strengthened`]) instead of Γ, so the same node under
//!   another Γ ending in the same entries is a hit. That is the shape a
//!   case tree's inner nodes have inside a motive re-checked at every level
//!   of a convoy: before, a family's index functions were judged once per
//!   level and per constructor. A check keeps it only when the expected type
//!   is syntax inside the same entries, and an inferred type only when it
//!   is, since a description is relative to Γ's length. The table that
//!   answers "which entries" is the bounds memo's function on its own
//!   table (`bounds::scope_term_use`), so it moves no substitution counter.
//! - **Successes only.** A failure propagates and records nothing.
//! - **Off under the spelling record** ([`spell_checked_in_code`]), whose
//!   point is to visit every checked spelling.
//! - Debug builds re-judge a sample of hits (`crate::checks`) and assert the
//!   memo's answer, out of the counters' sight (`crate::stats::unobserved`),
//!   so debug and release builds count alike.
//! - **Locally closed types are kept apart from Γ** ([`TyScope`],
//!   `issues/mutual-group-recursion-gate-cost.md`). A type with no free
//!   local variable and no weakening tail `wk^k_g`
//!   (`bounds::type_locally_closed`) reads nothing of Γ but its base, by
//!   weakening and strengthening, so its level is kept under a key that
//!   drops Γ's identity and keeps the rest of [`Scope`]. The case on a sum
//!   checks both summand types and is nested once per summand, so a closed
//!   sum spelled in an inductive's shape is judged at every case of every
//!   tree over that shape, in a Γ one binder longer each time: a mutual
//!   group's signature carries several such trees in every occurrence of the
//!   family, and judging the shape's tails there was most of the group's
//!   gate. Substitution shares a closed subtree (`bounds.rs`), so the node
//!   keeps its identity under every binder. Closedness is decided at a
//!   node's second judgment, never its first, so one-shot types pay one
//!   table entry and no bounds walk; the decision is a function of the
//!   sequence of nodes judged, so counts stay deterministic. An `IWf`
//!   signature is kept the same way ([`SigScope`]), so a locally closed
//!   family's signature is judged once per base context however many
//!   binders its occurrences sit under.
//! - **So are conversions between closed sides** ([`closed_side`],
//!   `issues/iwf-shape-spine-comb-depth.md`). A conversion whose two sides
//!   read nothing of Γ but its base (locally closed types, which a global
//!   reference at the empty substitution is) is kept under the cross-head
//!   memo's key less Γ's identity. A type spelled by its
//!   registered code, `El(D#tycode^δ)`, against its inline lowering is the
//!   case: a structural recursion's case tree met it once per node, each
//!   under one more binder, and each decoded the code and walked the sum.
//!   Successes only, sampled hits re-converted in debug builds.

use std::cell::{Cell, RefCell};
use std::collections::HashMap;
use std::hash::{Hash, Hasher};
use std::mem::{discriminant, Discriminant};
use std::sync::Arc as Rc;

pub(crate) mod ity;

use ity::{ITy, ITyRef, Sel, SndOf, TyForm};

use crate::conv::{
    conv_ity_cached, head_ity_cached, injection_heads_cached, projection_heads_cached, ConvError, ITyHead,
};
#[cfg(not(feature = "value-metrics"))]
use crate::conv::{conv_local_ctx_cached, conv_type_cached};
#[cfg(feature = "value-metrics")]
use crate::conv::{conv_local_ctx_cached_with_metrics, conv_type_cached_with_metrics};
use crate::layer::Layer;
use crate::premises::PremiseQueue;
use crate::level::Level;
use crate::rec::{self, gtm, gty, inst_tm_motive, inst_ty_motive, shift_univ_psi};
use crate::reduce::{whnf_type_delta, Defs, GlobalCache};
use crate::subst::{GlobalEntry, GlobalSubst};
use crate::term::{
    inst_motive2, iwf_children_ty, iwf_motive_scrut_ty, iwf_step_telescope, m_out_ty, m_step_ty, wf_step_telescope,
    CtxBase, IWfSig, MSig, CtxEntries, CtxEntriesIdentity, CtxEntry, GlobalBinding,
    GlobalCtx, GlobalVar, LocalCtx, LocalSubst, LocalVar, SubstTail, Term, Type,
};
use crate::value::{PtrMap, ValueMetrics};

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
    UnboundGlobalVar(GlobalVar),
    /// A reference that names a binding by the other spelling than the one
    /// Ψ gives it: an index reaching into the signature, or a position past
    /// it (DESIGN.md, "Constants are addressed from the start of Ψ").
    MisspelledGlobal(GlobalVar),
    /// The global binding at this index has the wrong kind (e.g. `U^δ`
    /// hitting a `g : Ctx` or `u : Trm` binding).
    WrongGlobalBinding(GlobalVar),
    /// A rule was used at a layer that does not admit it (layer-m former
    /// below m, non-variable term at layer v, binding layer `i' > i`, or a
    /// binding whose declared layer is outside its admissible set).
    LayerMismatch,
    /// A `box` in inference position: its contextual type is not inferable.
    /// Also an *unannotated* checked spelling in inference position, which
    /// is checking-only for the same reason (design §2.1).
    NotInferable,
    /// A checked spelling (`pair@`, `inl@`, `inr@`, `fst@`, `snd@`) inside
    /// the payload of a `box`. The code recursors range over exactly that
    /// payload and their branch telescopes type a pair's field
    /// sub-structures by the Σ's *components*, which a whole-type annotation
    /// does not give them (design §2.2–2.3), so the payload of a quotation
    /// carries only the component spellings.
    UnderBox,
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
///
/// Each binding is checked in the prefix before it, read with `psi`'s own
/// split: the first [`GlobalCtx::consts`] as the signature growing, the
/// rest as variables over it.
pub fn check_global_ctx(psi: &GlobalCtx, univs: u32, fuel: u64) -> R {
    let tc = Tc::new(fuel);
    let consts = psi.consts();
    let prefix = check_global_bindings(&tc, GlobalCtx::default(), psi.bindings.iter().take(consts), univs, true)?;
    check_global_bindings(&tc, prefix, psi.bindings.iter().skip(consts), univs, false)?;
    Ok(())
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
    check_global_bindings(&tc, prefix.clone(), extension.iter(), univs, false)?;
    Ok(())
}

/// [`check_global_ctx_extension`] for an extension of the **signature**:
/// `prefix` has no variable, and each binding of `extension` is checked as
/// the constant it will be committed as ([`GlobalCtx::commit`]), over the
/// prefix and the constants before it.
pub fn check_signature_extension(
    prefix: &GlobalCtx,
    extension: &[GlobalBinding],
    univs: u32,
    fuel: u64,
) -> R {
    let tc = Tc::new(fuel);
    check_global_bindings(&tc, prefix.clone(), extension.iter(), univs, true)?;
    Ok(())
}

fn check_global_bindings<'a>(
    tc: &Tc,
    mut prefix: GlobalCtx,
    bindings: impl IntoIterator<Item = &'a GlobalBinding>,
    univs: u32,
    commit: bool,
) -> R<GlobalCtx> {
    for b in bindings {
        let env = binding_env(&prefix, univs);
        check_global_binding_declaration(tc, &env, b)?;
        if let GlobalBinding::Tm { ctx, layer, ty, level, body: Some(t) } = b {
            tc.tm_check_rc(&env.in_ctx(ctx.clone(), *layer), t, ty, level)?;
        }
        drop(env);
        if commit {
            prefix.commit(b.clone());
        } else {
            prefix.push(b.clone());
        }
    }
    Ok(prefix)
}

fn binding_env(prefix: &GlobalCtx, univs: u32) -> Env {
    Env {
        psi: prefix.clone(),
        cache: Rc::new(GlobalCache::for_psi(prefix)),
        gamma: LocalCtx::nil(),
        layer: Layer::Prog,
        univs,
        under_box: false,
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
        cache: Rc::new(GlobalCache::for_psi(psi)),
        gamma: LocalCtx::nil(),
        layer,
        univs,
        under_box: false,
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
        psi: psi.clone(), cache: Rc::new(GlobalCache::for_psi(psi)), gamma: gamma.clone(), layer, univs, under_box: false,
        #[cfg(feature = "value-metrics")]
        value_metrics: None,
    };
    Tc::new(fuel).ty_check_syn(&env, ty, level)
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
        psi: psi.clone(), cache: Rc::new(GlobalCache::for_psi(psi)), gamma: gamma.clone(), layer, univs, under_box: false,
        #[cfg(feature = "value-metrics")]
        value_metrics: Some(_metrics.clone()),
    };
    Tc::new(fuel).ty_check_syn(&env, ty, level)
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
        psi: psi.clone(), cache: Rc::new(GlobalCache::for_psi(psi)), gamma: gamma.clone(), layer, univs, under_box: false,
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
        psi: psi.clone(), cache: Rc::new(GlobalCache::for_psi(psi)), gamma: gamma.clone(), layer, univs, under_box: false,
        #[cfg(feature = "value-metrics")]
        value_metrics: None,
    };
    Tc::new(fuel).tm_check_ty(&env, &Rc::new(t.clone()), ty, level)
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
        psi: psi.clone(), cache: Rc::new(GlobalCache::for_psi(psi)), gamma: gamma.clone(), layer, univs, under_box: false,
        #[cfg(feature = "value-metrics")]
        value_metrics: Some(_metrics.clone()),
    };
    Tc::new(fuel).tm_check_ty(&env, &Rc::new(t.clone()), ty, level)
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
        psi: psi.clone(), cache: Rc::new(GlobalCache::for_psi(psi)), gamma: gamma.clone(), layer, univs, under_box: false,
        #[cfg(feature = "value-metrics")]
        value_metrics: None,
    };
    let (ty, l) = Tc::new(fuel).tm_infer_syn(&env, &Rc::new(t.clone()))?;
    Ok(((*ty).clone(), l))
}

/// Where a refused [`check_term`] or [`check_type`] failed: the innermost
/// term whose check did not hold, the type it was checked at, and — when
/// the check reached the conversion its rule ends in — the type it was
/// inferred at. What [`locate_refusal`] returns.
///
/// **Presentation, never judgement.** The verdict is the gate's; this is the
/// answer to "where", for a caller that has to say it and recorded no site
/// of its own (`issues/elab-accepts-conjunction-for-equation.md`). Every
/// field is kernel syntax scoped where the check ran: `gamma` in full, and Ψ
/// as long as `psi_len`, which is longer than the gate's own Ψ under a
/// `letbox` or a meta-function binder.
#[derive(Clone, Debug)]
pub struct RefusedSite {
    pub psi_len: usize,
    pub layer: Layer,
    pub gamma: LocalCtx,
    pub term: Term,
    /// `None` when the expected type was a selection that did not spell.
    pub expected: Option<Type>,
    /// `None` when the check failed before its closing conversion — a λ at a
    /// non-Π, a domain that disagrees, an error inside inference.
    pub inferred: Option<Type>,
    pub level: Level,
    pub err: TypeError,
}

/// Run [`check_term`] again, recording where it fails: the innermost
/// failing check, or `None` when the check passes (or fails only outside
/// every term check — a level, a context). Costs one more kernel check, so
/// it belongs on the path of a refusal already decided, never on a gate.
#[allow(clippy::too_many_arguments)]
pub fn locate_refusal(
    psi: &GlobalCtx,
    univs: u32,
    layer: Layer,
    gamma: &LocalCtx,
    t: &Term,
    ty: &Type,
    level: &Level,
    fuel: u64,
) -> Option<RefusedSite> {
    let env = Env {
        psi: psi.clone(), cache: Rc::new(GlobalCache::for_psi(psi)), gamma: gamma.clone(), layer, univs, under_box: false,
        #[cfg(feature = "value-metrics")]
        value_metrics: None,
    };
    let tc = Tc::with_mode(fuel, TcMode::Locate { slot: RefCell::new(None) });
    let verdict = tc.tm_check_ty(&env, &Rc::new(t.clone()), ty, level);
    verdict.err()?;
    tc.mode.into_refused()
}

/// [`locate_refusal`] for [`check_type`]: the innermost *term* check under
/// the type that failed, if the failure was inside one.
pub fn locate_type_refusal(
    psi: &GlobalCtx,
    univs: u32,
    layer: Layer,
    gamma: &LocalCtx,
    ty: &Type,
    level: &Level,
    fuel: u64,
) -> Option<RefusedSite> {
    let env = Env {
        psi: psi.clone(), cache: Rc::new(GlobalCache::for_psi(psi)), gamma: gamma.clone(), layer, univs, under_box: false,
        #[cfg(feature = "value-metrics")]
        value_metrics: None,
    };
    let tc = Tc::with_mode(fuel, TcMode::Locate { slot: RefCell::new(None) });
    let verdict = tc.ty_check_syn(&env, ty, level);
    verdict.err()?;
    tc.mode.into_refused()
}

/// A checked spelling's former, as the eager checker viewed it: what the
/// translation `⌊·⌋` (`docs/intro-by-type-design.md` §2.4) writes into the
/// component form in its place.
#[derive(Clone, PartialEq, Eq)]
pub(crate) enum Spelled {
    Sigma { fst_level: Level, snd_level: Level, fst: Rc<Type>, snd: Rc<Type> },
    Sum { lhs_level: Level, rhs_level: Level, lhs: Rc<Type>, rhs: Rc<Type> },
    Pi { dom_level: Level, cod_level: Level, dom: Rc<Type>, cod: Rc<Type> },
}

/// One node for each component type the record holds twice. The checker
/// views each checked spelling at its own expected type, so the record holds
/// a fresh copy of the same type for every spelling viewed at it (a class's
/// record `Σ`, once per pair in a proof about it); rebuilt unshared, the
/// copies multiply the term by their size, and every later pass and reader
/// walks each one. Copies are found by the bounded `Debug` spelling
/// (`fmt.rs`) and then compared in full.
fn share_spelled(rec: &mut HashMap<(usize, u32), Option<Spelled>>) {
    let mut seen: HashMap<String, Vec<Rc<Type>>> = HashMap::new();
    let mut one = |t: &mut Rc<Type>| {
        let same = seen.entry(format!("{t:?}")).or_default();
        match same.iter().find(|u| ***u == **t) {
            Some(u) => *t = Rc::clone(u),
            None => same.push(Rc::clone(t)),
        }
    };
    for s in rec.values_mut().flatten() {
        match s {
            Spelled::Sigma { fst: a, snd: b, .. } | Spelled::Sum { lhs: a, rhs: b, .. } | Spelled::Pi { dom: a, cod: b, .. } => {
                one(a);
                one(b);
            }
        }
    }
}

/// Record `spelled` at `key`, or mark the key ambiguous (`None`) when the
/// node was already viewed at a different former.
fn keep_spelled(rec: &RefCell<HashMap<(usize, u32), Option<Spelled>>>, key: (usize, u32), spelled: Spelled) {
    let mut rec = rec.borrow_mut();
    match rec.get_mut(&key) {
        None => {
            rec.insert(key, Some(spelled));
        }
        Some(slot) => {
            if slot.as_ref() != Some(&spelled) {
                *slot = None;
            }
        }
    }
}

/// **The quote boundary** (`docs/intro-by-type-design.md` §2.3, amended
/// 2026-09-22): `t : ty @ level` in `gamma` with every checked spelling
/// translated to its component form, so it can be the payload of a `box`.
///
/// A payload elaborated inside a quotation is written in the component
/// forms already; what brings a checked spelling in is a term built
/// *outside* and pasted in — a callee's statement copied into an
/// application's annotations, a solution, a reduct. This is `⌊·⌋` of §2.4,
/// computed by the checker that already spells every component: the eager
/// mode checks `t`, keeps the former it viewed at each checked spelling, and
/// the term is rebuilt with those components. A kept component may carry
/// checked spellings of its own (a type's whnf unfolds definitions written
/// outside a quote), and the rebuilt component form `ty_check`s it, so the
/// pass repeats until nothing is left.
///
/// **Not trusted.** The result is checked under the `box` rule like any
/// payload, so a wrong translation is a refusal and never an acceptance.
/// Returns `t` itself when it holds no checked spelling.
#[allow(clippy::too_many_arguments)]
pub fn spell_checked_in_code(
    psi: &GlobalCtx,
    univs: u32,
    layer: Layer,
    gamma: &LocalCtx,
    t: Rc<Term>,
    ty: &Type,
    level: &Level,
    fuel: u64,
) -> R<Rc<Term>> {
    spell_checked(psi, univs, layer, gamma, t, ty, level, fuel, true)
}

/// [`spell_checked_in_code`] for an **export**: the introductions `pair@`,
/// `inl@`, `inr@` only. An export target reads `app@` as an application and
/// `fst@`/`snd@` as its own projections, which take the pair's type from the
/// pair, so none of the three has annotations to write. Spelling them is
/// what makes the passes cascade on a library proof
/// (`docs/export-fragment-design.md` §5.6): an `app@`'s components are the
/// callee's statement instantiated at the arguments, and a projection's are
/// the rest of a class record, whose later field statements mention the
/// earlier fields as `fst@`s of the record. Each instantiation carries
/// spellings of its own, which the next pass spells again, and their
/// annotations grow exponentially with the field index
/// (issues/export-spelling-cost.md).
#[allow(clippy::too_many_arguments)]
pub fn spell_checked_for_export(
    psi: &GlobalCtx,
    univs: u32,
    layer: Layer,
    gamma: &LocalCtx,
    t: Rc<Term>,
    ty: &Type,
    level: &Level,
    fuel: u64,
) -> R<Rc<Term>> {
    spell_checked(psi, univs, layer, gamma, t, ty, level, fuel, false)
}

#[allow(clippy::too_many_arguments)]
fn spell_checked(
    psi: &GlobalCtx,
    univs: u32,
    layer: Layer,
    gamma: &LocalCtx,
    t: Rc<Term>,
    ty: &Type,
    level: &Level,
    fuel: u64,
    all: bool,
) -> R<Rc<Term>> {
    const PASSES: usize = 16;
    let base = gamma.entries.len() as u32;
    let mut t = t;
    for _ in 0..PASSES {
        if crate::subst::count_checked_spellings(&t, all) == 0 {
            return Ok(t);
        }
        let tc = Tc::with_mode(fuel, TcMode::Spell { all, record: RefCell::new(HashMap::new()) });
        let env = Env {
            psi: psi.clone(),
            cache: Rc::new(GlobalCache::for_psi(psi)),
            gamma: gamma.clone(),
            layer,
            univs,
            under_box: false,
            #[cfg(feature = "value-metrics")]
            value_metrics: None,
        };
        tc.tm_check_ty(&env, &t, ty, level)?;
        let mut spelled = tc.mode.into_spellings();
        share_spelled(&mut spelled);
        let (next, replaced) = crate::subst::rebuild_checked_spellings(&t, &spelled, base, all);
        // `replaced` counts the nodes unshared for an ambiguous record too:
        // the next pass sees each occurrence on its own.
        if replaced == 0 {
            // Checked, yet a checked spelling was never visited at a depth
            // the walk can name: refuse as the `box` rule would.
            return Err(TypeError::UnderBox);
        }
        t = next;
    }
    Err(TypeError::UnderBox)
}

/// [`spell_checked_in_code`] for a **type** at `level`: the payload of a
/// `box` over a type — a statement handed to the reflection API.
pub fn spell_checked_in_code_ty(
    psi: &GlobalCtx,
    univs: u32,
    layer: Layer,
    gamma: &LocalCtx,
    t: Rc<Type>,
    level: &Level,
    fuel: u64,
) -> R<Rc<Type>> {
    spell_checked_ty(psi, univs, layer, gamma, t, level, fuel, true)
}

/// [`spell_checked_for_export`] for a type.
pub fn spell_checked_for_export_ty(
    psi: &GlobalCtx,
    univs: u32,
    layer: Layer,
    gamma: &LocalCtx,
    t: Rc<Type>,
    level: &Level,
    fuel: u64,
) -> R<Rc<Type>> {
    spell_checked_ty(psi, univs, layer, gamma, t, level, fuel, false)
}

#[allow(clippy::too_many_arguments)]
fn spell_checked_ty(
    psi: &GlobalCtx,
    univs: u32,
    layer: Layer,
    gamma: &LocalCtx,
    t: Rc<Type>,
    level: &Level,
    fuel: u64,
    all: bool,
) -> R<Rc<Type>> {
    const PASSES: usize = 16;
    let base = gamma.entries.len() as u32;
    let mut t = t;
    for _ in 0..PASSES {
        if crate::subst::count_checked_spellings_ty(&t, all) == 0 {
            return Ok(t);
        }
        let tc = Tc::with_mode(fuel, TcMode::Spell { all, record: RefCell::new(HashMap::new()) });
        let env = Env {
            psi: psi.clone(),
            cache: Rc::new(GlobalCache::for_psi(psi)),
            gamma: gamma.clone(),
            layer,
            univs,
            under_box: false,
            #[cfg(feature = "value-metrics")]
            value_metrics: None,
        };
        tc.ty_check(&env, &t, level)?;
        let mut spelled = tc.mode.into_spellings();
        share_spelled(&mut spelled);
        let (next, replaced) = crate::subst::rebuild_checked_spellings_ty(&t, &spelled, base, all);
        // `replaced` counts the nodes unshared for an ambiguous record too:
        // the next pass sees each occurrence on its own.
        if replaced == 0 {
            return Err(TypeError::UnderBox);
        }
        t = next;
    }
    Err(TypeError::UnderBox)
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
        Tc::eager(fuel).tm_check_ty(&oracle_env(psi, univs, layer, gamma), &Rc::new(t.clone()), ty, level)
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
            Tc::eager(fuel).tm_infer_syn(&oracle_env(psi, univs, layer, gamma), &Rc::new(t.clone()))?;
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
        Tc::eager(fuel).ty_check_syn(&oracle_env(psi, univs, layer, gamma), ty, level)
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
            cache: Rc::new(GlobalCache::for_psi(psi)),
            gamma: gamma.clone(),
            layer,
            univs,
            under_box: false,
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
        psi: psi.clone(), cache: Rc::new(GlobalCache::for_psi(psi)), gamma: gamma.clone(), layer, univs, under_box: false,
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
    /// Inside the payload of a `box`: the side condition on the two `box`
    /// rules that keeps the checked spellings out of code
    /// (`docs/intro-by-type-design.md` §2.3), read by
    /// [`Tc::checked_spelling_admitted`].
    ///
    /// **Not a layer predicate**, and that is the whole of stage 2's first
    /// stop: Heather checks *every* declaration body at `Layer::Code`
    /// (`crates/elab/src/lib.rs` ~3637), so `layer.computes()` is false at
    /// every emitter and a layer guard refuses the spellings everywhere. The
    /// recursors range over box payloads and nothing else, which is exactly
    /// what this bit names. It is sticky: nothing inside a payload returns
    /// to a computing layer (the two `box` rules are layer-m, so no box
    /// nests inside one), so no rule clears it.
    under_box: bool,
    #[cfg(feature = "value-metrics")]
    value_metrics: Option<ValueMetrics>,
}

impl Env {
    /// The scope's [`Ambient`]. The pattern names every field, so a field
    /// added to `Env` does not compile until it is either keyed here or
    /// said not to be read by any rule.
    #[inline]
    fn ambient(&self) -> Ambient {
        let Env {
            psi,
            // A cache of `psi`'s rescoped bodies: what it answers is fixed
            // by `psi`.
            cache: _,
            gamma,
            layer,
            univs,
            under_box,
            #[cfg(feature = "value-metrics")]
            value_metrics: _,
        } = self;
        Ambient {
            psi: psi.bindings.identity_addr(),
            // Γ's entries are keyed apart: by identity in a [`Scope`], and
            // not at all in a closed type's key, which reads none.
            gamma_base: match gamma.base {
                CtxBase::Nil => None,
                CtxBase::Var(g) => Some(g.key()),
            },
            univs: *univs,
            layer: *layer,
            under_box: *under_box,
        }
    }

    /// Replace Γ (and the layer) — for premises stated in a different local
    /// context, e.g. `Ψ; Δ ⊢_p T @ l`.
    fn in_ctx(&self, gamma: LocalCtx, layer: Layer) -> Env {
        Env { gamma, layer, ..self.clone() }
    }

    /// [`Env::in_ctx`] for the payload of a `box`: the same context switch,
    /// plus the side condition of design §2.3.
    fn in_box_ctx(&self, gamma: LocalCtx, layer: Layer) -> Env {
        Env { gamma, layer, under_box: true, ..self.clone() }
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
        // Ψ changed, so a cached entry's index denotes a different binding:
        // keeping the old cache here — body or signature alike — would be a
        // soundness bug, not a slowdown (and `Defs::transparent_cached` would
        // not consult it). Conversion's `push_tele` rebuilds for the same
        // reason.
        let cache = Rc::new(GlobalCache::for_psi(&psi));
        Env {
            psi,
            cache,
            gamma: self.gamma.shift_univ(tu).shift_global(tg),
            layer: self.layer,
            univs: self.univs + tu,
            under_box: self.under_box,
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
/// Whether `delta` is the identity on a source of as many entries as it has
/// terms: every entry the variable that names it (`LocalSubst::id`'s
/// expansion). The caller holds the count to the source's.
fn is_identity(delta: &LocalSubst) -> bool {
    let m = delta.terms.len();
    delta.terms.iter().enumerate().all(|(k, t)| matches!(&**t, Term::Var(v) if v.0 as usize == m - 1 - k))
}

/// The binding `v` names, when `v` is Ψ's spelling of it (`Σ; Ψ′ ⊢ c_p` needs
/// `p < |Σ|`, `u_i` needs `i < |Ψ′|`): the reference rule of DESIGN.md,
/// "Constants are addressed from the start of Ψ". A variable's statement is
/// scoped over its *prefix* of Ψ and callers weaken it by `v + 1`; a
/// constant's is read as stored ([`GlobalCache::sig`]).
fn lookup(psi: &GlobalCtx, v: GlobalVar) -> R<&GlobalBinding> {
    // Whatever `v` reaches, spelled or not, so that a reference to a binding
    // that is there is told apart from one to nothing.
    let Some(binding) = v.position(psi.bindings.len()).and_then(|at| psi.bindings.get(at)) else {
        return Err(TypeError::UnboundGlobalVar(v));
    };
    if !psi.spells(v) {
        return Err(TypeError::MisspelledGlobal(v));
    }
    Ok(binding)
}

// ---------------------------------------------------------------------------
// The checker
// ---------------------------------------------------------------------------

struct Tc {
    /// Per-conversion / per-normalization budget (see module docs).
    fuel: u64,
    /// Which of its four checkers this is ([`TcMode`]).
    mode: TcMode,
    /// Successful conversions whose syntax has different outer constructors.
    /// The cache lives for one public kernel gate; identity keys own every `Rc`
    /// they identify, so allocator reuse cannot create an aliasing key.
    conv_memo: RefCell<PtrMap<ConvMemoBucket, Vec<ConvMemo>>>,
    conv_memo_entries: Cell<usize>,
    /// Successful conversions of two [`closed_side`]s, kept apart from Γ
    /// (module docs, §The typing memo): the same pair met under another
    /// binder is the same judgment.
    closed_convs: RefCell<PtrMap<ClosedConvBucket, Vec<(Type, Type, Level)>>>,
    /// The typing memo (module docs, §The typing memo): per node and scope,
    /// for this gate.
    judged: RefCell<PtrMap<Scope, Judged>>,
    /// How many [`Tc::tm_check`]s are open on the native stack.
    check_depth: Cell<u32>,
    /// Checks deferred past [`crate::term::SPINE_ITERATE_AT`] open checks
    /// ([`crate::premises`]): a checking premise only answers yes or no, so
    /// a rule's premises are a conjunction whose order is free, and a check
    /// reached that deep is queued instead of descended into. The outermost
    /// open check drains the queue, at depth zero, before it answers — so no
    /// verdict leaves the checker with a queued premise unjudged, and a deep
    /// data value (a long list's spine) is checked by a loop rather than one
    /// native frame per node. A refusal from an outermost check that queued
    /// any forgets the memos ([`Tc::forget_after_refusal`]).
    deferred: RefCell<PremiseQueue<(Env, Rc<Term>, ITy, Level)>>,
    /// The strengthened scopes' telescopes, interned one entry at a time
    /// from the outermost of the `k` (§The typing memo): `(parent id, entry
    /// type's address)` to the entry's level, its keep-alive and the
    /// extended telescope's id. Id 0 is the empty telescope.
    teles: RefCell<PtrMap<(usize, usize), Vec<(Level, Rc<Type>, usize)>>>,
    /// The last telescope id handed out.
    tele_ids: Cell<usize>,
    /// The closed-type memo (module docs, §The typing memo): per shared
    /// type node and scope less Γ.
    closed_tys: RefCell<PtrMap<TyScope, ClosedTyEntry>>,
    /// The locally closed `IWf` signatures judged well-formed, by identity
    /// and scope less Γ, with their keep-alives.
    closed_sigs: RefCell<PtrMap<SigScope, (Rc<IWfSig>, Rc<()>)>>,
    /// The `var` rule's answers: an entry's type weakened past the entries
    /// after it, by the type's node and how many there are, with the node
    /// kept so that the address stays its. A variable is read many times
    /// under one scope, and each reading walked and allocated the type
    /// again; kept, the readings also share one node, which is what the
    /// memos keyed by a type's address and the reflexivity shortcut want.
    weakened: RefCell<PtrMap<(usize, u32), (Rc<Type>, Rc<Type>)>>,
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
    /// A type code headed by a global: its index, not its allocation. Such a
    /// term carries a local weakening that every substitution under a binder
    /// rewrites, so no two occurrences share an allocation, and an identity
    /// anchor would put each repeat of one query in a bucket of its own.
    Global(u32),
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

/// One side of a conversion that reads nothing of Γ but its base: a locally
/// closed type (`bounds::type_locally_closed`). A reference to Ψ at the
/// empty substitution is one, `U^·` or `El^l(u^·)`, and so is a sum of
/// those: an empty tail records no length (`term.rs`, `LocalSubst`), so the
/// occurrences under different binders are one spelling. Kept by value: a
/// closed type's `==` stops at its first shared child.
fn closed_side(t: &Type) -> Option<Type> {
    crate::bounds::type_ref_locally_closed(t).then(|| t.clone())
}

/// A [`Tc::closed_convs`] bucket: [`ConvMemoBucket`]'s, less Γ's identity,
/// which neither side reads.
#[derive(Clone, PartialEq, Eq, Hash)]
struct ClosedConvBucket {
    expected: Discriminant<Type>,
    inferred: Discriminant<Type>,
    psi: RcIdentity<()>,
    gamma_base: Option<u32>,
    layer: Layer,
    univs: u32,
}

/// Everything a typing rule reads from its scope besides Γ's entries: the
/// part of [`Env`] every typing memo key ([`Scope`], [`TyScope`],
/// [`SigScope`]) holds, so a component added here is in all three by
/// construction ([`Env::ambient`], docs/kernel-implicit-state-review.md §3).
///
/// Ψ is held by its bindings' identity, which also stands for the parts of
/// Ψ that are not bindings. Changing the interface boundary
/// ([`GlobalCtx::withholding`]) gives the bindings a fresh identity. A
/// sealed proof kept later ([`GlobalCtx::seal_kept`]) does not, and need
/// not: it only adds δ-steps, so a judgment made before it still holds
/// after. The memo's addresses are kept valid by its entries' keep-alives.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
struct Ambient {
    psi: usize,
    gamma_base: Option<u32>,
    univs: u32,
    layer: Layer,
    under_box: bool,
}

/// A [`Judged`] entry's key: the node and its scope, by identity (module
/// docs, §The typing memo). The addresses are kept valid by the entry.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
struct Scope {
    node: usize,
    ambient: Ambient,
    /// Γ's identity token, or, in a strengthened scope, the interned id of
    /// the innermost `k` entries ([`Tc::strengthened`]).
    gamma: usize,
    /// Whether `gamma` is a telescope id rather than Γ's identity.
    strengthened: bool,
}

impl Scope {
    fn of(env: &Env, t: &Rc<Term>) -> Scope {
        Scope {
            node: Rc::as_ptr(t) as usize,
            ambient: env.ambient(),
            gamma: env.gamma.entries.identity_addr(),
            strengthened: false,
        }
    }
}

/// A [`Tc::closed_tys`] key: a type node by identity, and everything a rule
/// reads besides the node and Γ, which a locally closed type does not read
/// (module docs, §The typing memo).
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
struct TyScope {
    node: usize,
    ambient: Ambient,
}

impl TyScope {
    fn of(env: &Env, t: &Rc<Type>) -> TyScope {
        TyScope { node: Rc::as_ptr(t) as usize, ambient: env.ambient() }
    }
}

/// A [`Tc::closed_sigs`] key: [`TyScope`]'s, for a signature.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
struct SigScope {
    sig: usize,
    ambient: Ambient,
}

impl SigScope {
    fn of(env: &Env, sig: &Rc<IWfSig>) -> SigScope {
        SigScope { sig: Rc::as_ptr(sig) as usize, ambient: env.ambient() }
    }
}

/// What the closed-type memo knows of one [`TyScope`]: judged once and not
/// yet asked whether it is closed; open; or closed, at this level.
#[derive(Clone)]
enum ClosedTy {
    Seen,
    Open,
    Level(Level),
}

/// A [`Tc::closed_tys`] entry, with the keep-alives for its key's addresses.
struct ClosedTyEntry {
    _ty: Rc<Type>,
    _psi: Rc<()>,
    state: ClosedTy,
}

/// The types the closed-type memo keeps: the formers with children, whose
/// judgment is a walk. A leaf is cheaper to judge than to look up.
fn closed_memo_candidate(t: &Type) -> bool {
    !matches!(
        t,
        Type::Nat
            | Type::Ty(_)
            | Type::Unit { .. }
            | Type::Empty { .. }
            | Type::SEmpty { .. }
            | Type::CodeTy { .. }
            | Type::CodeTm { .. }
    )
}

/// What one node was judged to be in one [`Scope`]: its inferred type, and
/// the expected types it checked against. The first three fields are the
/// keep-alives for the key's addresses.
struct Judged {
    _node: Rc<Term>,
    _psi: Rc<()>,
    _gamma: CtxEntriesIdentity,
    inferred: Option<(ITy, Level)>,
    checked: Vec<(ITy, Level)>,
}

impl Judged {
    fn new(env: &Env, t: &Rc<Term>) -> Judged {
        Judged {
            _node: Rc::clone(t),
            _psi: env.psi.bindings.identity(),
            _gamma: env.gamma.entries.identity(),
            inferred: None,
            checked: Vec::new(),
        }
    }
}

/// The forms whose inference the memo keeps: the eliminations, the only
/// forms whose cost is not their own syntax (an application checks its
/// argument and instantiates a codomain, a projection views its receiver's
/// type, a recursor checks its motives and branches). They are also how
/// checking reaches a shared value, since checking an elimination is
/// inferring it. Kind, never count: see §The typing memo.
fn infer_memoized(t: &Term) -> bool {
    matches!(
        t,
        Term::App { .. }
            | Term::AppAt { .. }
            | Term::Fst { .. }
            | Term::Snd { .. }
            | Term::FstAt { .. }
            | Term::SndAt { .. }
            | Term::ElimNat { .. }
            | Term::J { .. }
            | Term::ElimSEmpty { .. }
            | Term::ElimSquash { .. }
            | Term::ElimEmpty { .. }
            | Term::Case { .. }
            | Term::ElimW { .. }
            | Term::ElimWf { .. }
            | Term::ElimIWf { .. }
            | Term::Out { .. }
            | Term::UApp { .. }
            | Term::CtxApp { .. }
            | Term::TyApp { .. }
            | Term::LetBoxTy { .. }
            | Term::LetBoxTm { .. }
            | Term::ElimCodeTy { .. }
            | Term::ElimCodeTm { .. }
    )
}

/// The forms the checker descends through in checking position, whose
/// check the memo keeps against each expected type: everything
/// [`Tc::tm_check_inner`] does not hand to inference.
fn check_memoized(t: &Term) -> bool {
    matches!(
        t,
        Term::Lam { .. }
            | Term::ULam { .. }
            | Term::CtxLam { .. }
            | Term::TyLam { .. }
            | Term::BoxTy(_)
            | Term::BoxTm(_)
            | Term::PairAt { ty: None, .. }
            | Term::InlAt { ty: None, .. }
            | Term::InrAt { ty: None, .. }
    )
}

/// Whether `held` is the expected type `ty`: [`ITy`]'s equality, the
/// conversion rule's reflexivity test, through the borrow.
fn same_expected(held: &ITy, ty: ITyRef) -> bool {
    match ty {
        ITyRef::Syn(t) => held.as_syn().is_some_and(|h| std::ptr::eq(h, t) || h == t),
        ITyRef::Ity(t) => held == t,
    }
}

fn owned_expected(ty: ITyRef) -> ITy {
    match ty {
        ITyRef::Syn(t) => ITy::Owned(t.clone()),
        ITyRef::Ity(t) => t.clone(),
    }
}

/// The kernel checker's four modes (issues/kernel-checker-mode-enum.md).
/// One value, so the arms ask a named question ([`TcMode::eager`],
/// [`TcMode::spellings`], [`TcMode::refused_slot`]) and the twelve
/// combinations of the four fields it replaced that no checker was built
/// with cannot be built.
enum TcMode {
    /// The gate: descriptions stay lazy, every memo is used.
    Gate,
    /// The differential oracle ([`Tc::eager`]): the gate's rules, with
    /// every description materialized at once.
    Oracle,
    /// The quote-boundary translation ([`spell_checked_in_code`],
    /// [`spell_checked_for_export`]): the oracle, recording the former it
    /// viewed at each checked spelling.
    Spell {
        /// Whether every checked spelling is recorded, or only the
        /// introductions the export spells.
        all: bool,
        /// At each checked spelling the checker visits, the components of
        /// the former it viewed, keyed by the node's address and Γ's
        /// length.
        ///
        /// The key names a node, not an occurrence: a node the term shares
        /// between two places at the same Γ length can be viewed at two
        /// different formers (a motive's `inl@`, and the same node in a
        /// branch annotation where the scrutinee is a constructor). Such a
        /// node's entry is `None`, and the rebuild unshares it for the next
        /// pass.
        record: RefCell<HashMap<(usize, u32), Option<Spelled>>>,
    },
    /// [`locate_refusal`]'s checker: the gate, keeping the innermost check
    /// that failed, the first time an error passes through
    /// [`Tc::tm_check`]. It bypasses the typing memo
    /// ([`Tc::tm_check_noting`]). A gate that succeeds, every gate the
    /// suite runs but its refusals, pays one untaken branch per failing
    /// check and nothing per passing one.
    Locate { slot: RefCell<Option<RefusedSite>> },
}

impl TcMode {
    /// Whether descriptions are materialized at once rather than kept
    /// lazy (**the oracle mode**, `docs/intro-by-type-design.md` §3.6).
    ///
    /// Under it an [`ITy::Sel`] is spelled the moment it would be formed,
    /// and the five `@` rules view their annotation through the rewriter,
    /// so the checker is the one that existed before descriptions did. That is what makes `tests/typing_differential.rs`
    /// test *only* the new thing — that evaluating a description and
    /// rewriting it agree.
    #[inline]
    fn eager(&self) -> bool {
        matches!(self, TcMode::Oracle | TcMode::Spell { .. })
    }

    /// The spelling record, on the quote-boundary translation's checker.
    #[inline]
    fn spellings(&self) -> Option<&RefCell<HashMap<(usize, u32), Option<Spelled>>>> {
        match self {
            TcMode::Spell { record, .. } => Some(record),
            _ => None,
        }
    }

    /// Whether every checked spelling is recorded; `true` off the spelling
    /// checker, where nothing is.
    #[inline]
    fn spell_all(&self) -> bool {
        !matches!(self, TcMode::Spell { all: false, .. })
    }

    /// [`locate_refusal`]'s slot, on its checker.
    #[inline]
    fn refused_slot(&self) -> Option<&RefCell<Option<RefusedSite>>> {
        match self {
            TcMode::Locate { slot } => Some(slot),
            _ => None,
        }
    }

    /// The spelling record, taken out of a spelling checker.
    fn into_spellings(self) -> HashMap<(usize, u32), Option<Spelled>> {
        match self {
            TcMode::Spell { record, .. } => record.into_inner(),
            _ => panic!("not a spelling checker"),
        }
    }

    /// The refusal found, taken out of a locating checker.
    fn into_refused(self) -> Option<RefusedSite> {
        match self {
            TcMode::Locate { slot } => slot.into_inner(),
            _ => None,
        }
    }
}

/// How many expected types one node keeps per scope. A node checked
/// against more distinct types than this in one scope pays from then on, as
/// it did before the memo; the bound is a count, so which checks hit stays
/// deterministic.
const CHECKED_PER_SCOPE: usize = 4;

/// The most innermost entries a strengthened scope keys on
/// ([`Tc::strengthened`]). A node with more free locals keeps Γ's identity.
const STRENGTHEN_MAX: u32 = 8;

impl Tc {
    fn new(fuel: u64) -> Tc {
        Tc::with_mode(fuel, TcMode::Gate)
    }

    /// The differential oracle's checker: [`Tc::new`] with §3.6's eager
    /// materialization ([`TcMode::eager`]).
    fn eager(fuel: u64) -> Tc {
        Tc::with_mode(fuel, TcMode::Oracle)
    }

    fn with_mode(fuel: u64, mode: TcMode) -> Tc {
        Tc {
            fuel,
            mode,
            conv_memo: RefCell::new(PtrMap::default()),
            conv_memo_entries: Cell::new(0),
            closed_convs: RefCell::new(PtrMap::default()),
            judged: RefCell::new(PtrMap::default()),
            check_depth: Cell::new(0),
            deferred: RefCell::new(PremiseQueue::new()),
            teles: RefCell::new(PtrMap::default()),
            tele_ids: Cell::new(0),
            closed_tys: RefCell::new(PtrMap::default()),
            closed_sigs: RefCell::new(PtrMap::default()),
            weakened: RefCell::new(PtrMap::default()),
            #[cfg(feature = "value-metrics")]
            diag_stack: RefCell::new(Vec::new()),
            #[cfg(feature = "value-metrics")]
            diag_term: RefCell::new(None),
            #[cfg(feature = "value-metrics")]
            query_trace_seen: Cell::new(0),
        }
    }

    /// The fall-through's closing conversion on [`locate_refusal`]'s
    /// checker, keeping the inferred type when it fails. Outlined for
    /// [`Tc::tm_check_noting`]'s reason.
    #[cold]
    #[inline(never)]
    fn conv_ty_noting(&self, env: &Env, t: &Term, ty: ITyRef, inferred: &ITy, l: &Level) -> R {
        let verdict = self.conv_ty(env, ty, inferred.as_ref(), l);
        if let Err(err) = verdict {
            self.note_refused(env, t, ty, inferred.as_syn(), l, err);
        }
        verdict
    }

    /// Keep the failing check at `t`, unless an inner one was kept already:
    /// an error propagates outward through every enclosing check, and the
    /// first to see it is the innermost. Cold, and out of line, so the
    /// recursion's frames do not carry it.
    #[cold]
    #[inline(never)]
    fn note_refused(&self, env: &Env, t: &Term, expected: ITyRef, inferred: Option<&Type>, l: &Level, err: TypeError) {
        let Some(slot) = self.mode.refused_slot() else { return };
        let mut slot = slot.borrow_mut();
        if slot.is_some() {
            return;
        }
        *slot = Some(RefusedSite {
            psi_len: env.psi.bindings.len(),
            layer: env.layer,
            gamma: env.gamma.clone(),
            term: t.clone(),
            expected: match expected.as_syn() {
                Some(e) => Some(e.clone()),
                None => expected.as_ity().and_then(|e| self.materialize(env, e).ok()).map(|e| (*e).clone()),
            },
            inferred: inferred.cloned(),
            level: l.clone(),
            err,
        });
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
    /// it is the α-test it has always been (in the shared size of the two
    /// sides, `syntax_eq.rs`), and two equal selections are the
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
                CtxBase::Var(g) => Some(g.key()),
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
        let closed = match (closed_side(expected), closed_side(inferred)) {
            (Some(a), Some(b)) => Some((
                ClosedConvBucket {
                    expected: expected_head,
                    inferred: inferred_head,
                    psi: RcIdentity::new(env.psi.bindings.identity()),
                    gamma_base: match env.gamma.base {
                        CtxBase::Nil => None,
                        CtxBase::Var(g) => Some(g.key()),
                    },
                    layer: env.layer,
                    univs: env.univs,
                },
                a,
                b,
            )),
            _ => None,
        };
        if let Some((key, a, b)) = &closed
            && self
                .closed_convs
                .borrow()
                .get(key)
                .is_some_and(|bucket| bucket.iter().any(|(x, y, level)| level == l && x == a && y == b))
        {
            crate::stats::conv_memo_hits(1);
            #[cfg(debug_assertions)]
            if crate::checks::verify_this_skip() {
                assert!(
                    crate::stats::unobserved(|| self.conv_ity(env, ITyRef::Syn(expected), ITyRef::Syn(inferred), l))
                        .is_ok(),
                    "the closed-conversion memo kept a pair that converting again rejects \
                     (term output suppressed: see CLAUDE.md)"
                );
            }
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
        if let Some((key, a, b)) = closed {
            if self.conv_memo_entries.get() < 4096 {
                let mut memo = self.closed_convs.borrow_mut();
                let bucket = memo.entry(key).or_default();
                if bucket.len() < 4 {
                    bucket.push((a, b, l.clone()));
                    self.conv_memo_entries.set(self.conv_memo_entries.get() + 1);
                }
            }
            return Ok(());
        }
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
        self.materialize_in(env, t, env.gamma.entries.len() as u32)
    }

    /// [`Tc::materialize`] of a description denoting in the Γ of length
    /// `depth`, as syntax scoped there.
    fn materialize_in(&self, env: &Env, t: &ITy, depth: u32) -> R<Rc<Type>> {
        match t {
            ITy::Syn(t) => Ok(Rc::clone(t)),
            ITy::Owned(t) => Ok(Rc::new(t.clone())),
            ITy::At { ty, depth: at } if *at == depth => Ok(Rc::clone(ty)),
            ITy::At { ty, depth: at } => {
                // A description is formed in a scope and read in that scope
                // or a longer one.
                let Some(by) = depth.checked_sub(*at) else { return Err(TypeError::HeadMismatch) };
                Ok(Rc::new(ty.shift_local(by)))
            }
            ITy::Sel { of, sel, at_depth } => {
                crate::stats::ity_materialized(1);
                let of_depth = sel.of_depth(*at_depth);
                let base = self.materialize_in(env, of, of_depth)?;
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
                    (Type::Pi { cod, .. }, Sel::App(a)) => Rc::new(
                        cod.apply_local(&LocalSubst::id(&gamma).extended(Rc::clone(a))),
                    ),
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
            Some(t) => self.view(env, t, !t.is_syn() && !self.mode.eager()),
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
        let form = self.view(env, &t, !self.mode.eager())?;
        Ok((t, form))
    }

    /// Design §3.4's `view_v`: [`Tc::view`] for the `@` rules, the value
    /// domain whether `t` is a selection or a spelling (and the rewriter
    /// under the eager mode). The projections' receiver type is the case
    /// that is a spelling: the type a `pair@^{T}` inferred, which is `T`.
    fn view_v(&self, env: &Env, t: &ITy) -> R<TyForm> {
        self.view(env, t, !self.mode.eager())
    }

    /// Keep `form`'s components for `t` when this checker is the quote
    /// boundary's translator ([`spell_checked_in_code`]). The eager mode's
    /// views are syntax, so a component that is still a selection means the
    /// translator is not in eager mode, and nothing is kept.
    fn record(&self, env: &Env, t: &Term, form: &TyForm) {
        let Some(rec) = self.mode.spellings() else { return };
        if !self.mode.spell_all() && matches!(t, Term::FstAt { .. } | Term::SndAt { .. } | Term::AppAt { .. }) {
            return;
        }
        let syn = |t: &ITy| match t {
            ITy::Syn(t) => Some(Rc::clone(t)),
            ITy::Owned(t) => Some(Rc::new(t.clone())),
            ITy::Sel { .. } | ITy::At { .. } => None,
        };
        let spelled = match form {
            TyForm::Sigma { fst_level, snd_level, fst, snd: SndOf::Syn(snd) } => {
                let Some(fst) = syn(fst) else { return };
                Spelled::Sigma {
                    fst_level: fst_level.clone(),
                    snd_level: snd_level.clone(),
                    fst,
                    snd: Rc::clone(snd),
                }
            }
            TyForm::Sum { lhs_level, rhs_level, lhs, rhs } => {
                let (Some(lhs), Some(rhs)) = (syn(lhs), syn(rhs)) else { return };
                Spelled::Sum {
                    lhs_level: lhs_level.clone(),
                    rhs_level: rhs_level.clone(),
                    lhs,
                    rhs,
                }
            }
            TyForm::Pi { dom_level, cod_level, dom, cod } => {
                let (Some(dom), Some(cod)) = (syn(dom), syn(cod)) else { return };
                Spelled::Pi {
                    dom_level: dom_level.clone(),
                    cod_level: cod_level.clone(),
                    dom,
                    cod,
                }
            }
            _ => return,
        };
        keep_spelled(rec, (t as *const Term as usize, env.gamma.entries.len() as u32), spelled);
    }

    /// [`Tc::view_v`] of a borrowed expected type — the unannotated intros'
    /// view. A bare spelling has no [`ITy`] behind the borrow, so one is
    /// built; that clone is on the `@` path only.
    fn view_expected_v(&self, env: &Env, t: ITyRef) -> R<TyForm> {
        match t.as_ity() {
            Some(t) => self.view_v(env, t),
            None => {
                let t = ITy::Owned(t.as_syn().expect("not a selection").clone());
                self.view_v(env, &t)
            }
        }
    }

    /// Reject everything at layer v except the forms listed in ch. 04's
    /// "Note on Layer v Rules".
    fn not_var_layer(&self, env: &Env) -> R {
        if env.layer == Layer::Var { Err(TypeError::LayerMismatch) } else { Ok(()) }
    }

    /// The checked spellings' guard (`docs/intro-by-type-design.md` §2.3):
    /// they may appear anywhere **but** inside the payload of a `box`.
    ///
    /// A δ-unfolding cannot smuggle one in either: δ inside a box is opaque
    /// in both directions (`definitions.rs`), so a definition body that
    /// contains a checked spelling never becomes part of a payload.
    ///
    /// Layer v refuses them as it refuses the component forms, which is the
    /// half of stage 1a's `computing_layer` guard that survives.
    fn checked_spelling_admitted(&self, env: &Env) -> R {
        self.not_var_layer(env)?;
        if env.under_box { Err(TypeError::UnderBox) } else { Ok(()) }
    }

    /// An `IWf` signature's premises, shared by its formation rule and its
    /// two term formers (heather-coq `wft_iwf`, `wf_supi`, `wf_elimIWf`):
    /// `I @ li`, `S @ l`, `(Γ, x : S) ⊢ n : Nat`, `(Γ, x : S) ⊢ o : I`,
    /// `(Γ, x : S, i : Fin n) ⊢ c : I`.
    ///
    /// Through the closed-type memo's signature table (module docs, §The
    /// typing memo) when the signature is locally closed: one signature is
    /// shared by the family type at every binder depth of an eliminator's
    /// step, and its premises are judged once per gate, not per occurrence.
    fn iwf_sig_wf(&self, env: &Env, sig: &Rc<IWfSig>) -> R {
        if self.mode.spellings().is_some() || !crate::bounds::iwf_sig_locally_closed(sig) {
            return self.iwf_sig_premises(env, sig);
        }
        let key = SigScope::of(env, sig);
        if self.closed_sigs.borrow().contains_key(&key) {
            crate::stats::typing_memo_hits(1);
            #[cfg(debug_assertions)]
            if crate::checks::verify_this_skip() {
                assert!(
                    crate::stats::unobserved(|| self.iwf_sig_premises(env, sig)).is_ok(),
                    "the signature memo kept a signature that judging it again rejects \
                     (term output suppressed: see CLAUDE.md)"
                );
            }
            return Ok(());
        }
        self.iwf_sig_premises(env, sig)?;
        self.closed_sigs.borrow_mut().insert(key, (Rc::clone(sig), env.psi.bindings.identity()));
        Ok(())
    }

    /// [`Tc::iwf_sig_wf`] past the memo: the premises themselves.
    fn iwf_sig_premises(&self, env: &Env, sig: &IWfSig) -> R {
        self.level_wf(env, &sig.level)?;
        self.level_wf(env, &sig.idx_level)?;
        self.ty_check(env, &sig.idx, &sig.idx_level)?;
        self.ty_check(env, &sig.shape, &sig.level)?;
        let e_x = env.push_entry(Rc::clone(&sig.shape), sig.level.clone());
        self.tm_check_ty(&e_x, &sig.arity, &Type::Nat, &Level::Zero)?;
        self.tm_check_ty(&e_x, &sig.out, &sig.idx.shift_local(1), &sig.idx_level)?;
        let e_xi = e_x.push_entry(Rc::new(Type::Fin { len: Rc::clone(&sig.arity) }), Level::Zero);
        self.tm_check_ty(&e_xi, &sig.child, &sig.idx.shift_local(2), &sig.idx_level)
    }

    /// An `M` signature's premises, shared by its formation rule and its two
    /// term formers (docs/kernel-coinduction-design.md §1.1): `I @ li`,
    /// `(Γ, i : I) ⊢ S @ l`, `(Γ, i, s : S) ⊢ P @ l'`,
    /// `(Γ, i, s, p : P) ⊢ o : I`.
    fn m_sig_wf(&self, env: &Env, sig: &MSig) -> R {
        self.level_wf(env, &sig.level)?;
        self.level_wf(env, &sig.pos_level)?;
        self.level_wf(env, &sig.idx_level)?;
        self.ty_check(env, &sig.idx, &sig.idx_level)?;
        let e_i = env.push_entry(Rc::clone(&sig.idx), sig.idx_level.clone());
        self.ty_check(&e_i, &sig.shape, &sig.level)?;
        let e_is = e_i.push_entry(Rc::clone(&sig.shape), sig.level.clone());
        self.ty_check(&e_is, &sig.pos, &sig.pos_level)?;
        let e_isp = e_is.push_entry(Rc::clone(&sig.pos), sig.pos_level.clone());
        self.tm_check_ty(&e_isp, &sig.next, &sig.idx.shift_local(3), &sig.idx_level)
    }

    fn meta_layer(&self, env: &Env) -> R {
        if env.layer == Layer::Meta { Ok(()) } else { Err(TypeError::LayerMismatch) }
    }

    // -- local contexts -----------------------------------------------------

    /// `⊢_i Γ` (in `env.psi`; `env.gamma` is irrelevant).
    fn ctx_wf(&self, env: &Env, layer: Layer, gamma: &LocalCtx) -> R {
        if let CtxBase::Var(g) = gamma.base {
            match lookup(&env.psi, g)? {
                GlobalBinding::Ctx => {}
                _ => return Err(TypeError::WrongGlobalBinding(g)),
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
        // The tail covers Δ's base: the empty tail the empty base, from any
        // Γ, and a weakening `wk^k_g` the base `g`, from a Γ of length `k`
        // over the same `g`.
        match (target.base, delta.tail) {
            (CtxBase::Nil, SubstTail::Empty) => {}
            (CtxBase::Var(g), SubstTail::Wk { len, ctx_var }) => {
                if len != env.gamma.entries.len() as u32 || ctx_var != g || env.gamma.base != CtxBase::Var(g) {
                    return Err(TypeError::SubstMismatch);
                }
            }
            _ => return Err(TypeError::SubstMismatch),
        }
        if delta.terms.len() != target.entries.len() {
            return Err(TypeError::SubstMismatch);
        }
        // The identity into Γ itself: `Γ ⊢ id_Γ : Γ` holds for every
        // well-formed Γ, which the environment is. A strategy, not a rule —
        // it decides the same judgement as the step cases below, which for
        // a global referenced in the context it was made in (a lifted proof,
        // a named value) instantiate every entry's type by a prefix of the
        // identity: quadratic in the context for no information.
        if *target == env.gamma && is_identity(delta) {
            return Ok(());
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
    fn ty_check_syn(&self, env: &Env, t: &Type, l: &Level) -> R {
        let inferred = self.ty_infer(env, t)?;
        self.lev_eq(l, &inferred)
    }

    /// [`Tc::ty_check_syn`] for a type held as shared syntax, through the
    /// closed-type memo (module docs, §The typing memo): a locally closed
    /// type's level is inferred once per gate, whatever Γ it recurs in.
    fn ty_check(&self, env: &Env, t: &Rc<Type>, l: &Level) -> R {
        if self.mode.spellings().is_some() || !closed_memo_candidate(t) {
            return self.ty_check_syn(env, t, l);
        }
        let key = TyScope::of(env, t);
        let seen = self.closed_tys.borrow().get(&key).map(|e| e.state.clone());
        let inferred = match seen {
            Some(ClosedTy::Level(level)) => {
                crate::stats::typing_memo_hits(1);
                #[cfg(debug_assertions)]
                if crate::checks::verify_this_skip() {
                    assert!(
                        crate::stats::unobserved(|| self.ty_infer(env, t)).is_ok_and(|again| again == level),
                        "the closed-type memo kept a level that judging the type again does \
                         not give (term output suppressed: see CLAUDE.md)"
                    );
                }
                level
            }
            Some(ClosedTy::Open) => return self.ty_check_syn(env, t, l),
            // Met once before: decide whether it is closed, and judge it.
            Some(ClosedTy::Seen) => {
                let level = if crate::bounds::type_locally_closed(t) {
                    let level = self.ty_infer(env, t)?;
                    ClosedTy::Level(level)
                } else {
                    ClosedTy::Open
                };
                let next = level.clone();
                if let Some(e) = self.closed_tys.borrow_mut().get_mut(&key) {
                    e.state = next;
                }
                match level {
                    ClosedTy::Level(level) => level,
                    _ => return self.ty_check_syn(env, t, l),
                }
            }
            None => {
                let level = self.ty_infer(env, t)?;
                self.closed_tys.borrow_mut().insert(
                    key,
                    ClosedTyEntry {
                        _ty: Rc::clone(t),
                        _psi: env.psi.bindings.identity(),
                        state: ClosedTy::Seen,
                    },
                );
                level
            }
        };
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
            // DVec-formation (extension; docs/iwf-former-design.md §1.1):
            // ⊢_i DVec^l(k; i. F) @ l ⟸ ⊢_i k : Nat @ 0,
            // (Γ, i : Fin k @ 0) ⊢_i F @ l. At every layer: `TmDVec` is its
            // code (design §6, §13 step 4).
            Type::DVec { level, len, fam } => {
                self.level_wf(env, level)?;
                self.tm_check_ty(env, len, &Type::Nat, &Level::Zero)?;
                let e_i = env.push_entry(Rc::new(Type::Fin { len: Rc::clone(len) }), Level::Zero);
                self.ty_check(&e_i, fam, level)?;
                Ok(level.clone())
            }
            // IWf-formation (extension; docs/iwf-former-design.md §1.2):
            // ⊢_i IWf^{l,li}(I; x:S. n; x. o; x i. c)(m) @ l ⊔ li ⟸ the
            // signature (`iwf_sig_wf`), ⊢_i m : I @ li. At every layer:
            // `TmIWf` is its code (design §6, §13 step 4).
            Type::IWf { sig, index } => {
                self.iwf_sig_wf(env, sig)?;
                self.tm_check_rc(env, index, &sig.idx, &sig.idx_level)?;
                Ok(sig.family_level())
            }
            // M-formation (extension; docs/kernel-coinduction-design.md
            // §1.1): ⊢_i M^{l,l',li}(I; i. S; i s. P; i s p. o)(j) @ l ⊔ l' ⊔
            // li ⟸ the signature (`m_sig_wf`), ⊢_i j : I @ li. Admitted at
            // every layer, as `Wf` is: `TmM` is its code
            // (docs/kernel-m-codes-design.md §0).
            Type::M { sig, index } => {
                self.m_sig_wf(env, sig)?;
                self.tm_check_rc(env, index, &sig.idx, &sig.idx_level)?;
                Ok(sig.family_level())
            }
            Type::GlobalTy { var, subst } => {
                let GlobalBinding::Ty { ctx, layer, level } = lookup(&env.psi, *var)? else {
                    return Err(TypeError::WrongGlobalBinding(*var));
                };
                // i' ∈ {c, p} is the binding invariant; i' ≤ i:
                if *layer > env.layer {
                    return Err(TypeError::LayerMismatch);
                }
                let level = level.clone();
                crate::stats::global_ref_rescopes(1);
                let sig = env.cache.sig(*var, ctx, None);
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
    fn tm_check(&self, env: &Env, t: &Rc<Term>, ty: ITyRef, l: &Level) -> R {
        let depth = self.check_depth.get();
        // At depth zero the queue is empty (the outermost check settles it
        // before returning, and a drain judges its items at depth one), so
        // only the threshold can defer there.
        if self.deferred.borrow().should_defer(depth) {
            return self.tm_check_deferred(env, t, ty, l);
        }
        let pushed = self.deferred.borrow().epoch();
        self.check_depth.set(depth + 1);
        let verdict = self.tm_check_here(env, t, ty, l);
        self.check_depth.set(depth);
        if depth != 0 {
            return verdict;
        }
        let verdict = match verdict {
            Ok(()) => self.drain_deferred(),
            Err(err) => {
                self.deferred.borrow_mut().drop_past(0);
                Err(err)
            }
        };
        if verdict.is_err() && self.deferred.borrow().queued_since(pushed) {
            self.forget_after_refusal();
        }
        verdict
    }

    /// The memos after a refused outermost check that queued premises: a
    /// node is memoized when its own frame's rules succeed, which with
    /// premises queued is before the whole verdict is in, so an entry made
    /// during a check that was then refused may stand on a queued premise
    /// that failed (or was never judged). Dropping them keeps every memo
    /// entry backed by a complete verdict for whatever this checker judges
    /// next; a refusal ends almost every gate, so this costs nothing that
    /// matters.
    #[cold]
    #[inline(never)]
    fn forget_after_refusal(&self) {
        self.judged.borrow_mut().clear();
        self.closed_tys.borrow_mut().clear();
        self.closed_sigs.borrow_mut().clear();
    }

    /// [`Tc::tm_check`]'s rules, judged on this frame.
    #[inline(always)]
    fn tm_check_here(&self, env: &Env, t: &Rc<Term>, ty: ITyRef, l: &Level) -> R {
        #[cfg(feature = "value-metrics")]
        let _frame = self.diag_enter(t, "check");
        if self.mode.refused_slot().is_some() {
            return self.tm_check_noting(env, t, ty, l);
        }
        if self.mode.spellings().is_none() && check_memoized(t) {
            return self.tm_check_memo(env, t, ty, l);
        }
        self.tm_check_inner(env, t, ty, l)
    }

    /// Queue a check met too deep to descend into ([`Tc::deferred`]).
    #[cold]
    #[inline(never)]
    fn tm_check_deferred(&self, env: &Env, t: &Rc<Term>, ty: ITyRef, l: &Level) -> R {
        self.deferred.borrow_mut().defer((env.clone(), Rc::clone(t), owned_expected(ty), l.clone()));
        Ok(())
    }

    /// Judge every queued check, each from depth zero (so each may queue
    /// more, which this loop also takes), stopping at the first refusal.
    #[cold]
    #[inline(never)]
    fn drain_deferred(&self) -> R {
        let drain = self.deferred.borrow_mut().begin_drain(0, 0);
        let verdict = loop {
            let Some(((env, t, ty, l), start)) = self.deferred.borrow_mut().pop(&drain) else { break Ok(()) };
            self.check_depth.set(1);
            let verdict = self.tm_check_here(&env, &t, ty.as_ref(), &l);
            self.check_depth.set(0);
            if let Err(err) = verdict {
                break Err(err);
            }
            self.deferred.borrow_mut().judged(start);
        };
        self.deferred.borrow_mut().end_drain(drain, verdict.is_ok());
        verdict
    }

    /// [`Tc::tm_check`] on [`locate_refusal`]'s checker: the same rules,
    /// keeping the failing check. Outlined, so the recursion every other
    /// checker goes through keeps its frame (one untaken branch).
    #[cold]
    #[inline(never)]
    fn tm_check_noting(&self, env: &Env, t: &Rc<Term>, ty: ITyRef, l: &Level) -> R {
        let verdict = if self.mode.spellings().is_none() && check_memoized(t) {
            self.tm_check_memo(env, t, ty, l)
        } else {
            self.tm_check_inner(env, t, ty, l)
        };
        if let Err(err) = verdict {
            self.note_refused(env, t, ty, None, l, err);
        }
        verdict
    }

    /// The scope `t` is judged in when only Γ's innermost entries can
    /// matter (§The typing memo): `t` holds no weakening tail and its
    /// free locals are the innermost `k`, and those `k` entries' types hold
    /// none either and are scoped within the `k` themselves. Then every rule
    /// judging `t` reads those entries and nothing else of Γ, so the
    /// judgment is the same in any Γ that ends in them. The key is the
    /// entries' types by identity and their levels, interned; `None` when
    /// the conditions fail or `k` is past [`STRENGTHEN_MAX`].
    fn strengthened(&self, env: &Env, t: &Rc<Term>) -> Option<(Scope, u32)> {
        let u = crate::bounds::scope_term_use(t);
        let k = u.bound;
        if u.has_wk || k > STRENGTHEN_MAX || k as usize > env.gamma.entries.len() {
            return None;
        }
        let mut entries: [Option<&CtxEntry>; STRENGTHEN_MAX as usize] = [None; STRENGTHEN_MAX as usize];
        for j in 0..k {
            let e = env.gamma.entries.nth_inner(j)?;
            let eu = crate::bounds::scope_type_use(&e.ty);
            if eu.has_wk || eu.bound + j + 1 > k {
                return None;
            }
            entries[j as usize] = Some(e);
        }
        let mut id = 0usize;
        let mut teles = self.teles.borrow_mut();
        for j in (0..k).rev() {
            let e = entries[j as usize].expect("filled above");
            let slot = teles.entry((id, Rc::as_ptr(&e.ty) as usize)).or_default();
            id = match slot.iter().find(|(l, _, _)| *l == e.level) {
                Some((_, _, child)) => *child,
                None => {
                    let child = self.tele_ids.get() + 1;
                    self.tele_ids.set(child);
                    slot.push((e.level.clone(), Rc::clone(&e.ty), child));
                    child
                }
            };
        }
        let mut scope = Scope::of(env, t);
        scope.gamma = id;
        scope.strengthened = true;
        Some((scope, k))
    }

    /// [`Tc::tm_check`] through the typing memo, for [`check_memoized`]
    /// forms. Outlined: the lookup's temporaries stay off the recursion
    /// cycle every other node goes through.
    #[inline(never)]
    fn tm_check_memo(&self, env: &Env, t: &Rc<Term>, ty: ITyRef, l: &Level) -> R {
        // A check is strengthened only when the expected type is syntax
        // within the same `k` entries: it is half the judgment.
        let strong = self.strengthened(env, t).filter(|(_, k)| {
            ty.as_syn().is_some_and(|e| {
                let u = crate::bounds::scope_type_ref_use(e);
                !u.has_wk && u.bound <= *k
            })
        });
        let scope = strong.map_or_else(|| Scope::of(env, t), |(s, _)| s);
        let hit = self.judged.borrow().get(&scope).is_some_and(|j| {
            j.checked.iter().any(|(held, level)| level == l && same_expected(held, ty))
        });
        if hit {
            crate::stats::typing_memo_hits(1);
            #[cfg(debug_assertions)]
            if crate::checks::verify_this_skip() {
                assert!(
                    crate::stats::unobserved(|| self.tm_check_inner(env, t, ty, l)).is_ok(),
                    "the typing memo kept a check that judging the node again refuses \
                     (term output suppressed: see CLAUDE.md)"
                );
            }
            return Ok(());
        }
        self.tm_check_inner(env, t, ty, l)?;
        let mut judged = self.judged.borrow_mut();
        let entry = judged.entry(scope).or_insert_with(|| Judged::new(env, t));
        if entry.checked.len() < CHECKED_PER_SCOPE {
            entry.checked.push((owned_expected(ty), l.clone()));
        }
        Ok(())
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
    fn tm_check_rc(&self, env: &Env, t: &Rc<Term>, ty: &Rc<Type>, l: &Level) -> R {
        self.tm_check(env, t, ITyRef::Syn(ty), l)
    }

    /// [`Tc::tm_check`] where the rule built the expected type itself and
    /// still owns it — see [`Tc::tm_check_rc`] for why neither copies it.
    #[inline(always)]
    fn tm_check_ty(&self, env: &Env, t: &Rc<Term>, ty: &Type, l: &Level) -> R {
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
        // The expected Π is presupposed well-formed, so a domain spelled as
        // its domain is a well-formed type at `pd` and needs neither the
        // judgment nor the conversion. An elaborator copies the expected
        // domain into the λ it builds, and a domain the size of a family's
        // signature is otherwise judged afresh under every binder it sits
        // under (`issues/mutual-group-recursion-gate-cost.md`). Not while
        // recording spellings: the domain's own checked spellings are
        // recorded by judging it.
        if self.mode.spellings().is_some() || ps.as_syn().is_none_or(|p| p != &**dom) {
            self.ty_check(env, dom, dom_level)?;
            self.conv_ty(env, ps.as_ref(), ITyRef::Syn(dom), dom_level)?;
        }
        let e = env.push_entry(Rc::clone(dom), dom_level.clone());
        self.tm_check(&e, body, pt.as_ref(), cod_level)
    }

    fn tm_check_inner(&self, env: &Env, t: &Rc<Term>, ty: ITyRef, l: &Level) -> R {
        match &**t {
            // box T : □(Δ ⊢ Ty l) @ 0 ⟸ Ψ; Δ ⊢_c T @ l
            Term::BoxTy(code) => {
                self.meta_layer(env)?;
                let Type::CodeTy { ctx, level } = self.whnf(env, ty)? else {
                    return Err(TypeError::HeadMismatch);
                };
                self.lev_eq(l, &Level::Zero)?;
                self.ty_check(&env.in_box_ctx(ctx, Layer::Code), code, &level)
            }
            // box t : □(Δ ⊢ T @ l) @ 0 ⟸ Ψ; Δ ⊢_c t : T @ l
            Term::BoxTm(code) => {
                self.meta_layer(env)?;
                let Type::CodeTm { ctx, ty, level } = self.whnf(env, ty)? else {
                    return Err(TypeError::HeadMismatch);
                };
                self.lev_eq(l, &Level::Zero)?;
                self.tm_check_rc(&env.in_box_ctx(ctx, Layer::Code), code, &ty, &level)
            }
            // The unannotated checked spellings: checking-only (design §2.1).
            Term::PairAt { ty: None, .. }
            | Term::InlAt { ty: None, .. }
            | Term::InrAt { ty: None, .. } => self.tm_check_at(env, t, ty, l),
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
                    *self.diag_term.borrow_mut() = Some((**t).clone());
                }
                if self.mode.refused_slot().is_some() {
                    return self.conv_ty_noting(env, t, ty, &inferred, l);
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
    fn tm_infer(&self, env: &Env, t: &Rc<Term>) -> R<(ITy, Level)> {
        #[cfg(feature = "value-metrics")]
        let _frame = self.diag_enter(t, "infer");
        if self.mode.spellings().is_none() && infer_memoized(t) {
            return self.tm_infer_memo(env, t);
        }
        self.tm_infer_fresh(env, t)
    }

    /// [`Tc::tm_infer`] through the typing memo, for [`infer_memoized`]
    /// forms; outlined as [`Tc::tm_check_memo`] is.
    #[inline(never)]
    fn tm_infer_memo(&self, env: &Env, t: &Rc<Term>) -> R<(ITy, Level)> {
        let strong = self.strengthened(env, t);
        let exact = Scope::of(env, t);
        let hit = {
            let judged = self.judged.borrow();
            strong
                .and_then(|(s, _)| judged.get(&s).and_then(|j| j.inferred.clone()))
                .or_else(|| judged.get(&exact).and_then(|j| j.inferred.clone()))
        };
        if let Some(judged) = hit {
            crate::stats::typing_memo_hits(1);
            #[cfg(debug_assertions)]
            if crate::checks::verify_this_skip() {
                assert!(
                    crate::stats::unobserved(|| self.tm_infer_fresh(env, t)).is_ok_and(|again| again == judged),
                    "the typing memo kept an inferred type that judging the node again does \
                     not give (term output suppressed: see CLAUDE.md)"
                );
            }
            return Ok(judged);
        }
        let judged = self.tm_infer_fresh(env, t)?;
        // A description is relative to Γ's length, and syntax outside the
        // `k` entries would mean something else elsewhere: either keeps the
        // exact scope.
        let scope = match strong {
            Some((s, k))
                if judged.0.as_syn().is_some_and(|ty| {
                    let u = crate::bounds::scope_type_ref_use(ty);
                    !u.has_wk && u.bound <= k
                }) =>
            {
                s
            }
            _ => exact,
        };
        self.judged
            .borrow_mut()
            .entry(scope)
            .or_insert_with(|| Judged::new(env, t))
            .inferred = Some(judged.clone());
        Ok(judged)
    }

    /// [`Tc::tm_infer`] past the memo: the rules themselves.
    #[inline(always)]
    fn tm_infer_fresh(&self, env: &Env, t: &Rc<Term>) -> R<(ITy, Level)> {
        // The checked spellings are the only rules whose inferred type may
        // be a *description* (`docs/intro-by-type-design.md` §3.2), so they
        // have their own dispatch and every other rule keeps returning
        // syntax — which is the sentence "no existing rule constructs a
        // `Sel`" made true by construction rather than by review.
        if matches!(
            &**t,
            Term::PairAt { .. }
                | Term::InlAt { .. }
                | Term::InrAt { .. }
                | Term::FstAt { .. }
                | Term::SndAt { .. }
                | Term::AppAt { .. }
        ) {
            return self.tm_infer_at(env, t);
        }
        if let Term::Var(x) = &**t {
            let Some(e) = env.gamma.entries.nth_inner(x.0) else {
                return Err(TypeError::UnboundLocalVar(x.0));
            };
            return Ok((ITy::Syn(self.weakened(&e.ty, x.0 + 1)), e.level.clone()));
        }
        let (ty, l) = self.tm_infer_inner(env, t)?;
        Ok((ITy::Owned(ty), l))
    }

    /// `ty` weakened by `by` entries, once per node and distance
    /// ([`Tc::weakened`], the field).
    fn weakened(&self, ty: &Rc<Type>, by: u32) -> Rc<Type> {
        let key = (Rc::as_ptr(ty) as usize, by);
        if let Some((_, weak)) = self.weakened.borrow().get(&key) {
            return Rc::clone(weak);
        }
        let weak = Rc::new(ty.shift_local(by));
        self.weakened.borrow_mut().insert(key, (Rc::clone(ty), Rc::clone(&weak)));
        weak
    }

    /// [`Tc::tm_infer`] with the inferred type **spelled**: the four λ
    /// inference arms, which have to put it inside a syntactic former, and
    /// the public [`infer_term`]. See [`Tc::materialize`].
    fn tm_infer_syn(&self, env: &Env, t: &Rc<Term>) -> R<(Rc<Type>, Level)> {
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
    fn tm_infer_at(&self, env: &Env, t: &Rc<Term>) -> R<(ITy, Level)> {
        match &**t {
            // -- checked spellings (extension; docs/intro-by-type-design.md)
            //
            // `pair@`, `inl@`, `inr@` with an annotation: one whole-type
            // annotation instead of the former's components. Each rule is
            // the component rule with the premise `ty_check(component,
            // level)` replaced by "view `T` and read the component off the
            // former", and the *un-reduced* `T` returned as the synthesized
            // type, which is what keeps every consumer lazy in δ. Without an
            // annotation there is nothing to synthesize and the form is
            // `NotInferable`, the verdict `box` already gets — it is checked
            // against the expected type instead ([`Tc::tm_check_at`]).
            //
            // The guard is the design's §2.3 and is what leaves the code
            // grammar and all 65 recursor branches alone: these forms do not
            // occur inside a `box`, so `code_eq` never meets one and
            // `rec.rs` needs no branch.
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
            Term::PairAt { ty: Some(ty), fst, snd } => {
                self.checked_spelling_admitted(env)?;
                let level = self.ty_infer(env, ty)?;
                let (ity, form) = self.view_at(env, ty)?;
                self.record(env, t, &form);
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
            Term::InlAt { ty: Some(ty), val } | Term::InrAt { ty: Some(ty), val } => {
                self.checked_spelling_admitted(env)?;
                let level = self.ty_infer(env, ty)?;
                let (ity, form) = self.view_at(env, ty)?;
                self.record(env, t, &form);
                let TyForm::Sum { lhs_level, rhs_level, lhs, rhs } = form else {
                    return Err(TypeError::HeadMismatch);
                };
                let (summand, summand_level) = if matches!(&**t, Term::InrAt { .. }) {
                    (rhs, rhs_level)
                } else {
                    (lhs, lhs_level)
                };
                self.tm_check(env, val, summand.as_ref(), &summand_level)?;
                crate::stats::intro_at_nodes(1);
                Ok((ity, level))
            }
            // `fst@(p) : S` — **no annotation at all** (design §2.1,
            // revised): the receiver infers its own type and the Σ is viewed
            // out of that, so a projection of a `pair@` costs the pair's
            // annotation and nothing more. This is the rule that made the
            // first draft's `fst@(T; p)` unnecessary: `T` was always the type
            // `p` already infers.
            Term::FstAt { pair } => {
                if !self.mode.eager() {
                    return self.projection_at_spine(env, t);
                }
                self.checked_spelling_admitted(env)?;
                let (pair_ty, _) = self.tm_infer(env, pair)?;
                let form = self.view_v(env, &pair_ty)?;
                self.record(env, t, &form);
                let TyForm::Sigma { fst_level, fst: fst_c, .. } = form else {
                    return Err(TypeError::HeadMismatch);
                };
                crate::stats::intro_at_nodes(1);
                Ok((fst_c, fst_level))
            }
            // `snd@(p) : U[fst@(p)/x]` — the substituted term is the checked
            // spelling again, so the inferred type stays source-shaped even
            // though `U` itself came out of the view.
            Term::SndAt { pair } => {
                if !self.mode.eager() {
                    return self.projection_at_spine(env, t);
                }
                self.checked_spelling_admitted(env)?;
                let (pair_ty, _) = self.tm_infer(env, pair)?;
                let form = self.view_v(env, &pair_ty)?;
                self.record(env, t, &form);
                let TyForm::Sigma { snd_level, snd: snd_c, .. } = form else {
                    return Err(TypeError::HeadMismatch);
                };
                let fst_p = Term::FstAt { pair: Rc::clone(pair) };
                crate::stats::intro_at_nodes(1);
                Ok((snd_c.at(&env.gamma, Rc::new(fst_p)), snd_level))
            }
            // `app@(f; a) : T[a/x]` (`docs/app-by-head-type-design.md` §3.1)
            // — no annotation: the Π is the one `f` infers. Relative to
            // `app`'s rule this drops the two `ty_check`s of the annotation
            // and the conversion of `f`'s type against it; the head's
            // inference is what that rule's `tm_check` of `f` paid anyway.
            //
            // **The fast path is today's checker.** A head whose inferred
            // type is literally a Π — a global's statement, a local's type,
            // the previous node of a spine — returns `T[a/x]` as syntax, the
            // same `apply_local` the `app` rule returns, so what follows
            // sees the syntax it always saw. Only a head whose type needs
            // reduction to show its Π (a projected record field, a
            // type-level definition) is viewed in the value domain and
            // answers a description: §3.3 of the intro design, the rewriter
            // never runs on a type that came through a checked spelling.
            //
            // A spine is typed as one walk (`Tc::app_at_spine`): while the
            // telescope stays a syntactic Π, each argument meets its domain
            // under the arguments before it, substituted at once, and the
            // codomain is instantiated once at the end — not the remaining
            // telescope per node, which carries a copy of every earlier
            // argument per mention.
            Term::AppAt { .. } => {
                self.checked_spelling_admitted(env)?;
                self.app_at_spine(env, t)
            }
            // An unannotated intro: checking-only, exactly as `box` is.
            _ => Err(TypeError::NotInferable),
        }
    }

    /// Infer the head once and view the projection receivers in one arena.
    /// The returned type remains an arena-free selection description; the
    /// eager oracle and quote translator keep the original per-node rules.
    fn projection_at_spine(&self, env: &Env, t: &Rc<Term>) -> R<(ITy, Level)> {
        self.checked_spelling_admitted(env)?;
        let mut selections = Vec::new();
        let mut head = t;
        loop {
            match &**head {
                Term::FstAt { pair } => {
                    selections.push(Sel::Fst);
                    head = pair;
                }
                Term::SndAt { pair } => {
                    selections.push(Sel::Snd(Rc::new(Term::FstAt { pair: Rc::clone(pair) })));
                    head = pair;
                }
                _ => break,
            }
        }
        selections.reverse();
        let depth = env.gamma.entries.len() as u32;
        let (mut ty, mut level) = match &**head {
            // A variable's type is its entry's, scoped in the entries before
            // it. The selections below are evaluated, where that scope costs
            // nothing; the `var` rule's answer is the same type shifted into
            // this one, node by node, once per spine.
            Term::Var(x) => {
                let Some(e) = env.gamma.entries.nth_inner(x.0) else {
                    return Err(TypeError::UnboundLocalVar(x.0));
                };
                (ITy::At { ty: Rc::clone(&e.ty), depth: depth - (x.0 + 1) }, e.level.clone())
            }
            _ => self.tm_infer(env, head)?,
        };
        let levels = projection_heads_cached(
            &env.psi, &env.gamma, env.layer.type_layer(), &ty, &selections, self.fuel,
            #[cfg(feature = "value-metrics")]
            env.value_metrics.as_ref(),
            Rc::clone(&env.cache),
        )?;
        let levels = levels.ok_or(TypeError::HeadMismatch)?;
        for (sel, (fst_level, snd_level)) in selections.into_iter().zip(levels) {
            level = match &sel { Sel::Fst => fst_level, _ => snd_level };
            ty = ITy::Sel { of: Rc::new(ty), sel, at_depth: depth };
            crate::stats::intro_at_nodes(1);
        }
        Ok((ty, level))
    }

    /// An `app@` spine `f(a₁, …, aₖ)`, innermost node first. `base[delta]`
    /// is the type so far while `delta` holds arguments not yet substituted
    /// into `base`, the rest of a syntactic Π telescope scoped under them;
    /// substituting all of them at once is the same syntax as one at a time.
    /// A node whose Π is not syntax, and every node while the checked
    /// spellings are recorded (each node's Π is recorded as it is met), is
    /// typed alone by [`Tc::app_at_node`].
    fn app_at_spine(&self, env: &Env, t: &Rc<Term>) -> R<(ITy, Level)> {
        let mut spine = Vec::new();
        let mut head = t;
        while let Term::AppAt { fun, arg } = &**head {
            spine.push((&**head, arg));
            head = fun;
        }
        let (mut ty, mut level) = self.tm_infer(env, head)?;
        let mut pending: Option<(Rc<Type>, LocalSubst)> = None;
        for &(node, arg) in spine.iter().rev() {
            if self.mode.spellings().is_none() {
                let pi = match &pending {
                    Some((base, _)) => Some(Rc::clone(base)),
                    None => match ty.as_syn() {
                        Some(pi @ Type::Pi { .. }) => Some(Rc::new(pi.clone())),
                        _ => None,
                    },
                };
                if let Some(pi) = pi
                    && let Type::Pi { dom_level, cod_level, dom, cod } = &*pi
                {
                    match &pending {
                        Some((_, delta)) => self.tm_check_rc(env, arg, &Rc::new(dom.apply_local(delta)), dom_level)?,
                        None => self.tm_check_rc(env, arg, dom, dom_level)?,
                    }
                    let delta = match pending.take() {
                        Some((_, delta)) => delta,
                        None => LocalSubst::id(&env.gamma),
                    };
                    pending = Some((Rc::clone(cod), delta.extended(Rc::clone(arg))));
                    level = cod_level.clone();
                    continue;
                }
            }
            if let Some((base, delta)) = pending.take() {
                ty = ITy::Owned(base.apply_local(&delta));
            }
            (ty, level) = self.app_at_node(env, node, ty, arg)?;
        }
        if let Some((base, delta)) = pending {
            ty = ITy::Owned(base.apply_local(&delta));
        }
        Ok((ty, level))
    }

    /// One `app@` node `t = app@(f; arg)`, `f` inferred as `fun_ty`.
    fn app_at_node(&self, env: &Env, t: &Term, fun_ty: ITy, arg: &Rc<Term>) -> R<(ITy, Level)> {
        if let Some(Type::Pi { dom_level, cod_level, dom, cod }) = fun_ty.as_syn() {
            if let Some(rec) = self.mode.spellings().filter(|_| self.mode.spell_all()) {
                keep_spelled(
                    rec,
                    (t as *const Term as usize, env.gamma.entries.len() as u32),
                    Spelled::Pi {
                        dom_level: dom_level.clone(),
                        cod_level: cod_level.clone(),
                        dom: Rc::clone(dom),
                        cod: Rc::clone(cod),
                    },
                );
            }
            self.tm_check_rc(env, arg, dom, dom_level)?;
            let ty = cod.apply_local(&LocalSubst::id(&env.gamma).extended(Rc::clone(arg)));
            return Ok((ITy::Owned(ty), cod_level.clone()));
        }
        let form = self.view_v(env, &fun_ty)?;
        self.record(env, t, &form);
        let TyForm::Pi { dom_level, cod_level, dom, cod } = form else {
            return Err(TypeError::HeadMismatch);
        };
        self.tm_check(env, arg, dom.as_ref(), &dom_level)?;
        // The eager mode's view is the rewriter's, so its codomain
        // is syntax and the result is too — which is what keeps that
        // mode today's checker on `app@`.
        let ty = match cod {
            ITy::Syn(cod) => ITy::Owned(
                cod.apply_local(&LocalSubst::id(&env.gamma).extended(Rc::clone(arg))),
            ),
            ITy::Owned(cod) => ITy::Owned(
                cod.apply_local(&LocalSubst::id(&env.gamma).extended(Rc::clone(arg))),
            ),
            ITy::Sel { .. } | ITy::At { .. } => ITy::Sel {
                of: Rc::new(fun_ty),
                sel: Sel::App(Rc::clone(arg)),
                at_depth: env.gamma.entries.len() as u32,
            },
        };
        Ok((ty, cod_level))
    }

    /// The three **unannotated** intros in checking position (design §3.4),
    /// the rules that make the round's win possible: the expected type is an
    /// [`ITy`] — for a field of an outer `pair@` a *description* and never a
    /// spelling — and the fields are checked against `Sel`s of it. Nothing
    /// here builds a type, so a constructor value nested n deep costs n
    /// nodes of syntax instead of `3.5ⁿ`.
    ///
    /// Outlined for the same reason as [`Tc::tm_check_lam`]: it holds a
    /// [`TyForm`] across a recursive descent, and leaving those temporaries
    /// in [`Tc::tm_check_inner`]'s frame would put them on the checker's
    /// recursion cycle whether or not an `@` form is being checked.
    #[inline(never)]
    fn tm_check_at(&self, env: &Env, t: &Term, ty: ITyRef, l: &Level) -> R {
        self.checked_spelling_admitted(env)?;
        match t {
            Term::PairAt { ty: None, fst, snd } => {
                let form = self.view_expected_v(env, ty)?;
                self.record(env, t, &form);
                let TyForm::Sigma { fst_level, snd_level, fst: fst_c, snd: snd_c } = form else {
                    return Err(TypeError::HeadMismatch);
                };
                self.lev_eq(l, &Level::join(fst_level.clone(), snd_level.clone()))?;
                self.tm_check(env, fst, fst_c.as_ref(), &fst_level)?;
                let snd_at = snd_c.at(&env.gamma, Rc::clone(fst));
                self.tm_check(env, snd, snd_at.as_ref(), &snd_level)?;
                crate::stats::intro_at_nodes(1);
                Ok(())
            }
            Term::InlAt { ty: None, .. } | Term::InrAt { ty: None, .. }
                if !self.mode.eager() && self.mode.spellings().is_none() =>
            {
                self.injection_at_spine(env, t, ty, l)
            }
            Term::InlAt { ty: None, val } | Term::InrAt { ty: None, val } => {
                let form = self.view_expected_v(env, ty)?;
                self.record(env, t, &form);
                let TyForm::Sum { lhs_level, rhs_level, lhs, rhs } = form else {
                    return Err(TypeError::HeadMismatch);
                };
                self.lev_eq(l, &Level::join(lhs_level.clone(), rhs_level.clone()))?;
                let (summand, summand_level) = if matches!(t, Term::InrAt { .. }) {
                    (rhs, rhs_level)
                } else {
                    (lhs, lhs_level)
                };
                self.tm_check(env, val, summand.as_ref(), &summand_level)?;
                crate::stats::intro_at_nodes(1);
                Ok(())
            }
            _ => unreachable!("tm_check_at is reached only for an unannotated intro"),
        }
    }

    /// A contiguous chain of unannotated injections checked against `ty`,
    /// its layers viewed in one arena ([`injection_heads_cached`]) — the intro
    /// twin of [`Tc::projection_at_spine`]. Per node, layer `j`'s type is a
    /// selection `j` deep and its view replays all `j`: a constructor value
    /// of an `n`-constructor declaration is up to `n − 1` injections deep, so
    /// that was Θ(k²) evaluation for the `k`-th constructor
    /// (`issues/wide-inductive-constructor-mention-cost.md`). The rules and
    /// the descriptions are the per-node ones; the eager oracle and the
    /// recording translator keep the per-node path.
    fn injection_at_spine(&self, env: &Env, t: &Term, ty: ITyRef, l: &Level) -> R {
        let layer = |t: &Term| match t {
            Term::InlAt { ty: None, val } => Some((Sel::Lhs, Rc::clone(val))),
            Term::InrAt { ty: None, val } => Some((Sel::Rhs, Rc::clone(val))),
            _ => None,
        };
        let (sel, mut val) = layer(t).expect("injection_at_spine is reached only for an injection");
        let mut selections = vec![sel];
        while let Some((sel, inner)) = layer(&val) {
            selections.push(sel);
            val = inner;
        }
        let mut expected = match ty.as_ity() {
            Some(t) => t.clone(),
            None => ITy::Owned(ty.as_syn().expect("not a selection").clone()),
        };
        let levels = injection_heads_cached(
            &env.psi, &env.gamma, env.layer.type_layer(), &expected, &selections, self.fuel,
            #[cfg(feature = "value-metrics")]
            env.value_metrics.as_ref(),
            Rc::clone(&env.cache),
        )?;
        let levels = levels.ok_or(TypeError::HeadMismatch)?;
        let depth = env.gamma.entries.len() as u32;
        let mut level = l.clone();
        for (sel, (lhs_level, rhs_level)) in selections.into_iter().zip(levels) {
            self.lev_eq(&level, &Level::join(lhs_level.clone(), rhs_level.clone()))?;
            level = match sel { Sel::Lhs => lhs_level, _ => rhs_level };
            expected = ITy::Sel { of: Rc::new(expected), sel, at_depth: depth };
            crate::stats::intro_at_nodes(1);
        }
        self.tm_check(env, &val, expected.as_ref(), &level)
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
                let GlobalBinding::Tm { ctx, layer, ty, level, .. } = lookup(&env.psi, *var)? else {
                    return Err(TypeError::WrongGlobalBinding(*var));
                };
                // i' ∈ {v, c} is the binding invariant; i' ≤ i:
                if *layer > env.layer {
                    return Err(TypeError::LayerMismatch);
                }
                let level = level.clone();
                crate::stats::global_ref_rescopes(1);
                let sig = env.cache.sig(*var, ctx, Some(ty));
                // The binding form fixes the kind at this index, so a `Tm`
                // lookup always finds the `Tm` signature.
                let Some(ty) = sig.ty.as_ref() else {
                    return Err(TypeError::WrongGlobalBinding(*var));
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
            // M-code (docs/kernel-m-codes-design.md §1): well-formed exactly
            // when its decoding is a well-formed `M` signature, since `El u`
            // at `l` checks `u : Ty l`; the index is a term of the decoded
            // index type. A code at every layer but v, like every code.
            // DVec-code (docs/iwf-former-design.md §6): DVec^l(k; i. f) : Ty l
            // ⟸ k : Nat, (Γ, i : Fin k) ⊢ f : Ty l. The length is a term of
            // the ambient scope, the family binds the position.
            Term::TmDVec { level, len, fam } => {
                self.not_var_layer(env)?;
                self.level_wf(env, level)?;
                self.tm_check_ty(env, len, &Type::Nat, &Level::Zero)?;
                let e_i = env.push_entry(Rc::new(Type::Fin { len: Rc::clone(len) }), Level::Zero);
                self.tm_check_ty(&e_i, fam, &Type::Ty(level.clone()), &Level::succ(level.clone()))?;
                Ok((Type::Ty(level.clone()), Level::succ(level.clone())))
            }
            // IWf-code (design §6): well-formed exactly when its decoding is
            // a well-formed `IWf` signature (`El u` at `l` checks `u : Ty l`),
            // and the index is a term of the decoded index type, as `TmM`.
            Term::TmIWf { level, idx_level, idx, shape, arity, out, child, index } => {
                self.not_var_layer(env)?;
                let sig = crate::term::iwf_sig_of_code(level, idx_level, idx, shape, arity, out, child);
                // Decoded afresh here, so there is no shared signature to key on.
                self.iwf_sig_premises(env, &sig)?;
                self.tm_check_rc(env, index, &sig.idx, &sig.idx_level)?;
                let family = sig.family_level();
                Ok((Type::Ty(family.clone()), Level::succ(family)))
            }
            Term::TmM { level, pos_level, idx_level, idx, shape, pos, next, index } => {
                self.not_var_layer(env)?;
                let sig = crate::term::m_sig_of_code(level, pos_level, idx_level, idx, shape, pos, next);
                self.m_sig_wf(env, &sig)?;
                self.tm_check_rc(env, index, &sig.idx, &sig.idx_level)?;
                let family = sig.family_level();
                Ok((Type::Ty(family.clone()), Level::succ(family)))
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
                let base_ty = motive.inst_top(0, &Term::Zero);
                self.tm_check_ty(env, base, &base_ty, level)?;
                // M[su x/x] scoped in (Γ, x : Nat, y : M).
                let su_x = Term::Succ(Rc::new(Term::Var(LocalVar(1))));
                let step_ty = motive.inst_top(2, &su_x);
                let e_xy = e_x.push_entry(Rc::clone(motive), level.clone());
                self.tm_check_ty(&e_xy, step, &step_ty, level)?;
                self.tm_check_ty(env, scrut, &Type::Nat, &Level::Zero)?;
                Ok((
                    motive.inst_top(0, scrut),
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
            // [b₀, …, b_{w-1}]^l(T; z, o) : Vec^l(T; w) @ l
            // (docs/bitvector-literal-entry-design.md §3.1). Two elements are
            // checked, not `w`: every element *is* `zero` or `one`, which is
            // what makes the literal the pair chain `vec_lit_unfold` spells
            // and lets that chain's typing be read off these premises. The
            // width is bounded by a word and no bit beyond it is set. Like
            // the checked spellings it is a compact spelling of a chain the
            // code recursors would have to see whole, so it is refused in a
            // `box` payload, whose recursors range over component forms.
            Term::VecLit { level, elem, zero, one, width, bits } => {
                self.checked_spelling_admitted(env)?;
                if !crate::term::vec_lit_in_range(*width, *bits) {
                    return Err(TypeError::HeadMismatch);
                }
                self.level_wf(env, level)?;
                self.ty_check(env, elem, level)?;
                self.tm_check_rc(env, zero, elem, level)?;
                self.tm_check_rc(env, one, elem, level)?;
                Ok((
                    Type::Vec {
                        level: level.clone(),
                        elem: Rc::clone(elem),
                        len: Rc::new(Term::NatLit(u64::from(*width).into())),
                    },
                    level.clone(),
                ))
            }
            // [e₀, …, e_{n-1}]^l(T) : Vec^l(T; n) @ l, n ≥ 1 — the premises
            // of the pair chain it spells (`term::vec_items_unfold`): `T` a
            // type at `l` and every element a `T`, the chain's `snd`
            // premises being `Vec`s of the same `T`. Checked in a loop, which
            // is the node's reason to exist: the chain recursed once per
            // element. A compact spelling like `VecLit`, so refused where
            // that is.
            Term::VecItems { level, elem, items, from } => {
                self.checked_spelling_admitted(env)?;
                let Some(live) = crate::term::vec_items_live(items, *from) else {
                    return Err(TypeError::HeadMismatch);
                };
                self.level_wf(env, level)?;
                self.ty_check(env, elem, level)?;
                for item in live {
                    self.tm_check_rc(env, item, elem, level)?;
                }
                Ok((
                    Type::Vec {
                        level: level.clone(),
                        elem: Rc::clone(elem),
                        len: Rc::new(Term::NatLit((live.len() as u64).into())),
                    },
                    level.clone(),
                ))
            }
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
                let left_ty = motive.inst_top(1, &inl_x);
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
                let right_ty = motive.inst_top(1, &inr_y);
                self.tm_check_ty(&e_y, case_r, &right_ty, motive_level)?;
                self.tm_check_ty(env, scrut, &sum, &lmax)?;
                Ok((
                    motive.inst_top(0, scrut),
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

            // sup_i^{l,li}(sig; a; cs) : IWf(sig)(o[a/x]) @ l ⊔ li, with
            // cs : DVec^{l⊔li}(n[a/x]; k. IWf(sig)(c[a/x, k/i])) — the
            // constructor is at its output index (docs/iwf-former-design.md
            // §2). A value at a convertible index checks by conversion. A code
            // at every layer but v, as `sup_f` is (design §13 step 4).
            Term::Supi { sig, label, children } => {
                self.not_var_layer(env)?;
                self.iwf_sig_wf(env, sig)?;
                self.tm_check_rc(env, label, &sig.shape, &sig.level)?;
                let fl = sig.family_level();
                self.tm_check_ty(env, children, &iwf_children_ty(sig, label), &fl)?;
                Ok((sig.at(Rc::new(sig.out.inst_top(0, label))), fl))
            }
            // elim_IWf^{l,li,l'}(sig; j z. M; a cs ih. s; m; t) : M[m/j, t/z]
            // @ l' (design §4). The motive ranges over every index; the step
            // telescope is `iwf_step_telescope`, the one transcription of
            // heather-coq's `iwfcsty`/`iwfihty`/`iwfstepty`. The telescope's
            // types are not checked: they are well-formed given the
            // signature and the motive (heather-coq `IWf_ihty_wf`).
            Term::ElimIWf { sig, motive_level, motive, step, index, scrut } => {
                self.not_var_layer(env)?;
                self.iwf_sig_wf(env, sig)?;
                self.level_wf(env, motive_level)?;
                let fl = sig.family_level();
                // M scoped in (Γ, j : I, z : IWf(…)(j)).
                let e_j = env.push_entry(Rc::clone(&sig.idx), sig.idx_level.clone());
                let e_jz = e_j.push_entry(Rc::new(iwf_motive_scrut_ty(sig)), fl.clone());
                self.ty_check(&e_jz, motive, motive_level)?;
                let (cs_ty, ih_ty, step_ty) = iwf_step_telescope(sig, motive_level, motive);
                let e_a = env.push_entry(Rc::clone(&sig.shape), sig.level.clone());
                let e_cs = e_a.push_entry(Rc::new(cs_ty), fl.clone());
                let e_step = e_cs.push_entry(Rc::new(ih_ty), motive_level.clone());
                self.tm_check_ty(&e_step, step, &step_ty, motive_level)?;
                self.tm_check_rc(env, index, &sig.idx, &sig.idx_level)?;
                self.tm_check_ty(env, scrut, &sig.at(Rc::clone(index)), &fl)?;
                Ok((inst_motive2(motive, 0, index, scrut), motive_level.clone()))
            }

            // corec^{k}(sig; i. X; i x. c; j; x) : M(sig)(j) @ f, with
            // (Γ, i) ⊢ X @ k, (Γ, i, x : X) ⊢ c : m_step_ty(…)↑ and
            // x : X[j/i] (docs/kernel-coinduction-design.md §1.3). The
            // carrier's level is free: one rule per k, quantifying over
            // nothing. Admitted at c (docs/kernel-m-codes-design.md §0): a
            // boxed corec is inert syntax, as a boxed `supf` is.
            Term::Corec { sig, carrier_level, carrier, step, index, seed } => {
                self.not_var_layer(env)?;
                self.m_sig_wf(env, sig)?;
                self.level_wf(env, carrier_level)?;
                let e_i = env.push_entry(Rc::clone(&sig.idx), sig.idx_level.clone());
                self.ty_check(&e_i, carrier, carrier_level)?;
                let fl = sig.family_level();
                let step_ty = m_step_ty(sig, carrier_level, carrier).shift_local(1);
                let e_ix = e_i.push_entry(Rc::clone(carrier), carrier_level.clone());
                let step_level = Level::join(sig.level.clone(), Level::join(carrier_level.clone(), fl.clone()));
                self.tm_check_ty(&e_ix, step, &step_ty, &step_level)?;
                self.tm_check_rc(env, index, &sig.idx, &sig.idx_level)?;
                self.tm_check_ty(env, seed, &carrier.inst_top(0, index), carrier_level)?;
                Ok((sig.at(Rc::clone(index)), fl))
            }
            // out(sig; j; m) : Σ(s : S[j]). Π(p : P[j, s]). M(sig)(o[j, s, p])
            // for m : M(sig)(j) (design §1.2).
            Term::Out { sig, index, scrut } => {
                self.not_var_layer(env)?;
                self.m_sig_wf(env, sig)?;
                self.tm_check_rc(env, index, &sig.idx, &sig.idx_level)?;
                let fl = sig.family_level();
                self.tm_check_ty(env, scrut, &sig.at(Rc::clone(index)), &fl)?;
                Ok((m_out_ty(sig, index), Level::join(sig.level.clone(), fl)))
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
            | Term::SndAt { .. }
            | Term::AppAt { .. } => Err(TypeError::NotInferable),

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
    /// scopes, and all 65 branches at their instantiated motive types.
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
        Term::TmDVec { .. } => "TmDVec",
        Term::TmIWf { .. } => "TmIWf",
        Term::TmM { .. } => "TmM",
        Term::Zero => "Zero",
        Term::NatLit(..) => "NatLit",
        Term::Succ(..) => "Succ",
        Term::ElimNat { .. } => "ElimNat",
        Term::Refl { .. } => "Refl",
        Term::J { .. } => "J",
        Term::SRefl { .. } => "SRefl",
        Term::Squash { .. } => "Squash",
        Term::ElimSEmpty { .. } => "ElimSEmpty",
        Term::ElimSquash { .. } => "ElimSquash",
        Term::Pair { .. } => "Pair",
        Term::VecLit { .. } => "VecLit",
        Term::VecItems { .. } => "VecItems",
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
        Term::Supi { .. } => "Supi",
        Term::ElimIWf { .. } => "ElimIWf",
        Term::Corec { .. } => "Corec",
        Term::Out { .. } => "Out",
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
        Term::AppAt { .. } => "AppAt",
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
            | Term::TmM { .. }
            | Term::TmDVec { .. }
            | Term::TmIWf { .. }
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
        Type::DVec { .. } => "DVec",
        Type::IWf { .. } => "IWf",
        Type::M { .. } => "M",
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
        Type::El { tm, .. } => {
            let mut head: &Term = tm;
            while let Term::App { fun, .. } | Term::AppAt { fun, .. } = head {
                head = fun;
            }
            match head {
                Term::GlobalTm { var, .. } => TypeAnchor::Global(var.key()),
                _ => TypeAnchor::Term(RcIdentity::new(Rc::clone(tm))),
            }
        }
        Type::Id { ty, .. } | Type::SEq { ty, .. } | Type::Squash { ty, .. } => {
            TypeAnchor::Type(RcIdentity::new(Rc::clone(ty)))
        }
        // A tuple and a vector anchor on their first element's type, which
        // is where a children tuple's repeated queries agree.
        Type::Sigma { fst, .. } => type_anchor(fst),
        Type::Sum { lhs, .. } => TypeAnchor::Type(RcIdentity::new(Rc::clone(lhs))),
        Type::W { shape, .. } | Type::Wf { shape, .. } => {
            TypeAnchor::Type(RcIdentity::new(Rc::clone(shape)))
        }
        Type::Vec { elem, .. } => type_anchor(elem),
        Type::DVec { fam, .. } => type_anchor(fam),
        Type::IWf { sig, .. } => TypeAnchor::Type(RcIdentity::new(Rc::clone(&sig.shape))),
        Type::M { sig, .. } => TypeAnchor::Type(RcIdentity::new(Rc::clone(&sig.shape))),
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
            cache: Rc::new(GlobalCache::for_psi(&psi)),
            psi,
            gamma: LocalCtx::nil(),
            layer: Layer::Prog,
            univs: 0,
            under_box: false,
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
                var: GlobalVar::index(v),
                subst: LocalSubst {
                    tail: SubstTail::Empty,
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
            var: GlobalVar::index(v),
            subst: LocalSubst {
                tail: SubstTail::Empty,
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
        let u1 = Rc::new(global_tm(1));
        assert_eq!(tc.tm_infer_syn(&outer, &u1).map(|(t, _)| (*t).clone()), Ok(Type::Nat));
        let pushed = outer.push_global(GlobalBinding::Ctx);
        assert_eq!(
            tc.tm_infer_syn(&pushed, &u1).map(|(t, _)| (*t).clone()),
            Ok(Type::Unit { level: Level::Zero }),
            "the signature cache survived a telescope push",
        );
        // And index 2 is the outer binding again, now needing `shift_global(3)`.
        assert_eq!(tc.tm_infer_syn(&pushed, &Rc::new(global_tm(2))).map(|(t, _)| (*t).clone()), Ok(Type::Nat));

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

/// The typing memo (module docs, §The typing memo), on a chain whose every
/// link uses the last one twice: `s₀ = 0`, `sᵢ = f(sᵢ₋₁, sᵢ₋₁)`, for a local
/// `f : Nat → Nat → Nat`. As a DAG it is `k` links; as a tree, `2^k` leaves.
#[cfg(test)]
mod typing_memo_tests {
    use super::*;
    use crate::stats;

    fn nat() -> Rc<Type> {
        Rc::new(Type::Nat)
    }

    fn arrow(dom: Rc<Type>, cod: Rc<Type>) -> Type {
        Type::Pi { dom_level: Level::Zero, cod_level: Level::Zero, dom, cod }
    }

    /// `f(a, b)` with `f` the innermost local, both applications annotated.
    fn f_of(a: &Rc<Term>, b: &Rc<Term>, result: &Rc<Type>) -> Rc<Term> {
        let partial = Rc::new(Term::App {
            fun: Rc::new(Term::Var(LocalVar(0))),
            dom_level: Level::Zero,
            cod_level: Level::Zero,
            dom: nat(),
            cod: Rc::new(arrow(nat(), Rc::clone(result))),
            arg: Rc::clone(a),
        });
        Rc::new(Term::App {
            fun: partial,
            dom_level: Level::Zero,
            cod_level: Level::Zero,
            dom: nat(),
            cod: Rc::clone(result),
            arg: Rc::clone(b),
        })
    }

    /// Every link of the chain, `s₀` first.
    fn chain(k: usize) -> Vec<Rc<Term>> {
        let mut links = vec![Rc::new(Term::Zero)];
        for _ in 0..k {
            let last = Rc::clone(links.last().unwrap());
            links.push(f_of(&last, &last, &nat()));
        }
        links
    }

    /// Γ = `f : Nat → Nat → result`.
    fn env_with_f(result: Rc<Type>) -> Env {
        let psi = GlobalCtx::default();
        Env {
            cache: Rc::new(GlobalCache::for_psi(&psi)),
            psi,
            gamma: LocalCtx::nil(),
            layer: Layer::Prog,
            univs: 0,
            under_box: false,
            #[cfg(feature = "value-metrics")]
            value_metrics: None,
        }
        .push_entry(Rc::new(arrow(nat(), Rc::new(arrow(nat(), result)))), Level::Zero)
    }

    fn queries(d: &stats::Snapshot) -> u64 {
        d.conv_shortcut_hits + d.conv_memo_hits + d.conv_misses
    }

    /// The acceptance shape: 40 links would be 2^40 paths, and checking the
    /// chain costs a constant number of judgments per link.
    #[test]
    fn a_shared_chain_is_judged_once_per_link() {
        let k = 40;
        let links = chain(k);
        let env = env_with_f(nat());
        let before = stats::snapshot();
        Tc::new(DEFAULT_FUEL).tm_check_ty(&env, &links[k], &Type::Nat, &Level::Zero).unwrap();
        let d = stats::snapshot().since(&before);
        // Every link but `s₀` (a literal) and `sₖ` (reached once) is reached
        // twice, and the second path is the hit.
        assert_eq!(d.typing_memo_hits, k as u64 - 1);
        assert!(queries(&d) <= 8 * k as u64, "{} conversion queries for {k} links", queries(&d));
    }

    /// A hit needs the same node in the same scope. The same node judged
    /// where `f` means something else is judged again, and refused, and a
    /// structurally equal but separately built Γ is a different scope.
    #[test]
    fn the_memo_answers_only_in_the_scope_it_was_filled() {
        let links = chain(6);
        let top = &links[6];
        let tc = Tc::new(DEFAULT_FUEL);
        let first = env_with_f(nat());
        tc.tm_check_ty(&first, top, &Type::Nat, &Level::Zero).unwrap();

        let unit = Rc::new(Type::Unit { level: Level::Zero });
        let other = env_with_f(Rc::clone(&unit));
        assert!(
            tc.tm_check_ty(&other, top, &Type::Nat, &Level::Zero).is_err(),
            "the memo answered for a Γ in which `f` returns Unit",
        );

        let before = stats::snapshot();
        tc.tm_check_ty(&env_with_f(nat()), top, &Type::Nat, &Level::Zero).unwrap();
        let fresh = stats::snapshot().since(&before);
        let before = stats::snapshot();
        tc.tm_check_ty(&first, top, &Type::Nat, &Level::Zero).unwrap();
        let again = stats::snapshot().since(&before);
        assert!(again.typing_memo_hits > 0, "the same node in the same Γ missed");
        assert!(
            queries(&fresh) > queries(&again),
            "an equal but separately built Γ was answered from the memo",
        );
    }

    /// Failures are not kept: a refused check leaves nothing that a later,
    /// correct check of the same node could hit, nor a stale success that a
    /// wrong one could.
    #[test]
    fn a_refusal_is_not_memoized() {
        let links = chain(4);
        let tc = Tc::new(DEFAULT_FUEL);
        let env = env_with_f(nat());
        let unit = Type::Unit { level: Level::Zero };
        assert!(tc.tm_check_ty(&env, &links[4], &unit, &Level::Zero).is_err());
        assert!(tc.judged.borrow().values().all(|j| j.checked.is_empty()));
        tc.tm_check_ty(&env, &links[4], &Type::Nat, &Level::Zero).unwrap();
        assert!(tc.tm_check_ty(&env, &links[4], &unit, &Level::Zero).is_err());
    }

    /// The strengthened scope: a node that reads only the innermost entries
    /// is answered from the memo under any Γ ending in those same entries,
    /// however much lies outside them. A chain checked once under `f` is
    /// all hits under `u : Unit, f` with the same `f`.
    #[test]
    fn a_node_is_judged_once_under_entries_it_cannot_see() {
        let links = chain(12);
        let tc = Tc::new(DEFAULT_FUEL);
        let inner = env_with_f(nat());
        tc.tm_check_ty(&inner, &links[12], &Type::Nat, &Level::Zero).unwrap();
        let f = inner.gamma.entries.last().unwrap().clone();
        let wider = Env { gamma: LocalCtx::nil(), ..inner.clone() }
            .push_entry(Rc::new(Type::Unit { level: Level::Zero }), Level::Zero)
            .push_entry(f.ty, f.level);
        let before = stats::snapshot();
        tc.tm_check_ty(&wider, &links[12], &Type::Nat, &Level::Zero).unwrap();
        let d = stats::snapshot().since(&before);
        assert!(d.typing_memo_hits > 0, "the chain was judged again under an entry it cannot see");
        // The one query left is the top's inferred type against `Nat`.
        assert!(queries(&d) <= 1, "the top link was not answered whole");
    }

    /// Kind, never count: holding an extra reference to every node (what the
    /// bounds cache's keep-alives do to an arbitrary subset) changes no
    /// counter, so which lookups hit does not depend on reference counts.
    #[test]
    fn reference_counts_do_not_move_the_counters() {
        let links = chain(12);
        let run = || {
            let before = stats::snapshot();
            Tc::new(DEFAULT_FUEL)
                .tm_check_ty(&env_with_f(nat()), &links[12], &Type::Nat, &Level::Zero)
                .unwrap();
            stats::snapshot().since(&before)
        };
        let plain = run();
        let held: Vec<Rc<Term>> = links.iter().flat_map(|l| [Rc::clone(l), Rc::clone(l)]).collect();
        let perturbed = run();
        drop(held);
        assert_eq!(plain, perturbed);
    }
}
