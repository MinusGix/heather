//! Algorithmic convertibility checking (docs/delam/06, §Convertibility
//! Checking): reduce both sides to WHNF with the untyped weak-head
//! reduction, then compare structurally, mutually across the nine
//! judgments of the chapter:
//!
//! | tex judgment                  | here            |
//! |-------------------------------|-----------------|
//! | `Γ ⊢ T ≈ T' : l`              | [`Conv::ty`]    |
//! | `Γ ⊢ W ≈ W' : l` (normal)     | [`Conv::ty_nf`] |
//! | `Γ ⊢ V ≈ V' : l` (neutral)    | [`Conv::ty_ne`] |
//! | `⊢ Γ ≈ Δ`                     | [`Conv::ctx`]   |
//! | `Γ ⊢ t ≈ t' : T @ l`          | [`Conv::tm`]    |
//! | `Γ ⊢ w ≈ w' : W @ l` (normal) | [`Conv::tm_nf`] |
//! | `Γ ⊢ ν ≈ ν' : T @ l` (neutral)| [`Conv::tm_ne`] |
//! | … with the type in WHNF       | [`Conv::tm_nee`]|
//! | `Γ ⊢ δ ≈ δ' : Δ`              | [`Conv::subst`] |
//!
//! Shape of the algorithm (on its well-typed inputs it **decides** ch. 06's
//! relation; the relation itself is transcribed rule for rule in `reduce.rs`,
//! per DESIGN.md):
//!
//! - **Neutral comparison is inference**: `tm_ne`/`ty_ne` return the type /
//!   universe level of the left input (left-biased — sound by ch. 08); the
//!   normal-form judgments are checking. Application and projection
//!   inference are **typed**: they compare the heads, read the Π / Σ the
//!   heads infer, and compare the argument at *its* domain — the stored
//!   `x:S.T` / Σ annotations are not related to each other, the mirror
//!   image of the ch. 06 note that ignores the *inferred* type instead
//!   (both are redundant on the well-typed inputs conversion presupposes;
//!   see the `App` arm of [`Conv::tm_ne`] for why the paper's choice was
//!   the expensive one). The judgment-level `l` inputs are threaded for rule
//!   fidelity but never branch the algorithm — every level the rules
//!   actually check is an *annotation*, compared via [`Level::equiv`].
//! - **η-directed** comparison at all four function types (`Π`, `ΠΠ`,
//!   `(g : Ctx) ⇒`, `(U : Typ) ⇒`): compare applications to a fresh
//!   variable in the suitably extended context.
//! - **Boxed types/terms compare syntactically** (`==`; α-equality is free
//!   under de Bruijn). Code is static data — β-convertible code is *not*
//!   convertible.
//! - Neutral recursors compare motives, all 56 branches (each at its
//!   instantiated motive type, the ch. 04 `G_A` telescopes), and indices —
//!   the ch. 06 `C_A` bundle ([`Conv::rec_ca`]).
//! - The layer index restricts *types*, not terms (ch. 06 intro): layer-m
//!   type formers mismatch outside layer m, but layer-m *term* forms are
//!   compared at any layer — their rules are stated at layer m, so those
//!   arms locally bump the layer to `m` (this is what lets conversion at
//!   layer p relate layer-m terms at MLTT types).
//! - **Fuel**: a single budget shared by all reduction steps and all
//!   comparison nodes, so the checker is total by construction even on
//!   ill-typed input; exhaustion is the distinguishable
//!   [`ConvError::OutOfFuel`]. On well-typed input conversion terminates
//!   (ch. 07/08), so exhaustion there means the budget was too small.
//!
//! Two apparent typos in the tex are deliberately not followed (both are
//! contradicted by the ch. 04 typing rules): the neutral `elim^Trm`
//! conclusion is at level `l₂` (the term-motive level), not `l₁`, and the
//! `t_app` branch type substitutes `u_s^id` (the argument) for the `Π`
//! codomain variable, not `u_t^id`.
//!
//! **What a weak head normal form *is* is abstract** ([`dom`]): the arms
//! reach their inputs through the [`dom::Dom`] accessor boundary. The public
//! entry points below instantiate it at [`dom::values::Values`], an
//! environment machine over the value domain of
//! `docs/nbe-conversion-design.md`; [`oracle`] instantiates the same arms at
//! [`dom::Syn`], the `reduce.rs` term rewriter, and exists only so the two
//! can be held against each other. Nothing above depends on the choice — the
//! rules, the fuel accounting, the left-biased inference and the layer
//! discipline are the same either way.

use std::collections::HashMap;
use std::marker::PhantomData;
use std::sync::Arc as Rc;

use crate::layer::Layer;
use crate::level::Level;
use crate::rec::{self, gtm, gty, shift_univ_psi};
use crate::reduce::{Defs, GlobalCache, Sig, NATIVE_DEPTH_LIMIT};
use crate::term::{
    Branches, CtxEntries, CtxEntry, GlobalBinding, GlobalCtx, GlobalVar, LocalCtx, LocalVar,
    Motives, Term, Type,
};
use crate::typing::ity::ITy;
use crate::value::{self, shift::Outer, TmClo, TyClo, ValueArena, VTy};
#[cfg(feature = "value-metrics")]
use crate::value::ValueMetrics;

mod dom;

use dom::{Dom, Syn, TmView, TyView, Values};

/// Why a convertibility check did not succeed.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ConvError {
    /// The shared fuel budget ran out before the check finished. On
    /// well-typed input this means the budget was too small; on untyped
    /// input it may be divergence.
    OutOfFuel,
    /// No rule relates the two inputs: they are not convertible.
    NotConvertible,
}

type R<T = ()> = Result<T, ConvError>;

const NC: ConvError = ConvError::NotConvertible;

/// `Ψ; Γ ⊢_i T ≈ T' : l` — convertibility of types.
/// Syntactic equality **modulo level equivalence** — the quotient DeLaM
/// ch. 05's Static Code lemma (`lem:dt:static`) takes over its equalities.
/// Used only to compare boxed code, where layer `c` does not compute and
/// equivalence therefore *is* equality.
trait CodeEq: PartialEq {
    fn normalized(&self) -> Self;
}

impl CodeEq for Type {
    fn normalized(&self) -> Type {
        self.normalize_levels()
    }
}

impl CodeEq for Term {
    fn normalized(&self) -> Term {
        self.normalize_levels()
    }
}

/// `a = b` modulo level equivalence. The `==` fast path keeps the common
/// case allocation-free; only genuinely different syntax pays for a rewrite.
fn code_eq<T: CodeEq>(a: &T, b: &T) -> bool {
    a == b || a.normalized() == b.normalized()
}

pub fn conv_type(
    psi: &GlobalCtx,
    gamma: &LocalCtx,
    layer: Layer,
    a: &Type,
    b: &Type,
    level: &Level,
    fuel: u64,
) -> R {
    debug_assert!(layer.computes(), "convertibility is only invoked at computing layers");
    let arena = ValueArena::new();
    Conv::<Values>::new(fuel, psi).ty_root(&Env::new(&arena, psi, gamma, layer), a, b, level)
}

/// `Ψ; Γ ⊢_i t ≈ t' : T @ l` — convertibility of terms at a type.
#[allow(clippy::too_many_arguments)]
pub fn conv_term(
    psi: &GlobalCtx,
    gamma: &LocalCtx,
    layer: Layer,
    a: &Term,
    b: &Term,
    ty: &Type,
    level: &Level,
    fuel: u64,
) -> R {
    debug_assert!(layer.computes(), "convertibility is only invoked at computing layers");
    let arena = ValueArena::new();
    Conv::<Values>::new(fuel, psi).tm_root(&Env::new(&arena, psi, gamma, layer), a, b, ty, level)
}

/// [`conv_term`] with allocation/cache/application metrics collected in the
/// same caller-owned region as profiled kernel typing.
#[cfg(feature = "value-metrics")]
#[allow(clippy::too_many_arguments)]
pub fn conv_term_profiled(
    psi: &GlobalCtx,
    gamma: &LocalCtx,
    layer: Layer,
    a: &Term,
    b: &Term,
    ty: &Type,
    level: &Level,
    fuel: u64,
    metrics: &ValueMetrics,
) -> R {
    debug_assert!(layer.computes(), "convertibility is only invoked at computing layers");
    let arena = ValueArena::profiled(metrics);
    Conv::<Values>::new(fuel, psi).tm_root(&Env::new(&arena, psi, gamma, layer), a, b, ty, level)
}

/// `Ψ ⊢_i Γ ≈ Δ` — convertibility of local contexts.
pub fn conv_local_ctx(
    psi: &GlobalCtx,
    layer: Layer,
    a: &LocalCtx,
    b: &LocalCtx,
    fuel: u64,
) -> R {
    debug_assert!(layer.computes(), "convertibility is only invoked at computing layers");
    let arena = ValueArena::new();
    let env = Env::new(&arena, psi, &LocalCtx::nil(), layer);
    Conv::<Values>::new(fuel, psi).ctx(&env, layer, a, b)
}

// -- entry points that borrow the caller's body cache ------------------------
//
// The four below are the entries `typing.rs` uses. They differ from the public
// ones above in one argument: a [`GlobalCache`] the *checker* owns, so the
// rescoped bodies a gate's definitions unfold to survive from one conversion
// query to the next instead of being rebuilt per query. The cache belongs to
// one Ψ (see [`GlobalCache`]), and the caller is the one that knows its Ψ is the
// same — `typing::Env` rebuilds it exactly where conversion's own `push_tele`
// does. `docs/conversion-query-arena-pooling-design.md` §3.

#[cfg(not(feature = "value-metrics"))]
#[allow(clippy::too_many_arguments)]
pub(crate) fn conv_type_cached(
    psi: &GlobalCtx,
    gamma: &LocalCtx,
    layer: Layer,
    a: &Type,
    b: &Type,
    level: &Level,
    fuel: u64,
    cache: Rc<GlobalCache>,
) -> R {
    debug_assert!(layer.computes(), "convertibility is only invoked at computing layers");
    let arena = ValueArena::new();
    let env = Env::new_with(&arena, psi, gamma, layer, cache);
    Conv::<Values>::new(fuel, psi).ty_root(&env, a, b, level)
}

#[cfg(feature = "value-metrics")]
#[allow(clippy::too_many_arguments)]
pub(crate) fn conv_type_cached_with_metrics(
    psi: &GlobalCtx,
    gamma: &LocalCtx,
    layer: Layer,
    a: &Type,
    b: &Type,
    level: &Level,
    fuel: u64,
    metrics: Option<&ValueMetrics>,
    cache: Rc<GlobalCache>,
) -> R {
    debug_assert!(layer.computes(), "convertibility is only invoked at computing layers");
    let arena = metrics.map_or_else(ValueArena::new, ValueArena::profiled);
    let env = Env::new_with(&arena, psi, gamma, layer, cache);
    Conv::<Values>::new(fuel, psi).ty_root(&env, a, b, level)
}

#[cfg(not(feature = "value-metrics"))]
pub(crate) fn conv_local_ctx_cached(
    psi: &GlobalCtx,
    layer: Layer,
    a: &LocalCtx,
    b: &LocalCtx,
    fuel: u64,
    cache: Rc<GlobalCache>,
) -> R {
    debug_assert!(layer.computes(), "convertibility is only invoked at computing layers");
    let arena = ValueArena::new();
    let env = Env::new_with(&arena, psi, &LocalCtx::nil(), layer, cache);
    Conv::<Values>::new(fuel, psi).ctx(&env, layer, a, b)
}

#[cfg(feature = "value-metrics")]
pub(crate) fn conv_local_ctx_cached_with_metrics(
    psi: &GlobalCtx,
    layer: Layer,
    a: &LocalCtx,
    b: &LocalCtx,
    fuel: u64,
    metrics: Option<&ValueMetrics>,
    cache: Rc<GlobalCache>,
) -> R {
    debug_assert!(layer.computes(), "convertibility is only invoked at computing layers");
    let arena = metrics.map_or_else(ValueArena::new, ValueArena::profiled);
    let env = Env::new_with(&arena, psi, &LocalCtx::nil(), layer, cache);
    Conv::<Values>::new(fuel, psi).ctx(&env, layer, a, b)
}

// -- entry points that take the checker's *descriptions* ---------------------
//
// `docs/intro-by-type-design.md` §3.3: an [`ITy`] is consumed by exactly two
// operations, and both of them are a per-query arena's worth of value-domain
// work. The arena's lifetime is unchanged — it is built here and dropped
// when the query returns, exactly as `conv_type_cached`'s is — which is the
// whole point of the checker holding descriptions rather than values
// (§3.7, and the stage-1b measurement that withdrew the migration).
//
// Neither is reached on a declaration with no `@` form: every existing rule
// produces `ITy::Syn`, `Tc::conv_ty` routes a `Syn`-against-`Syn` query to
// `conv_type_cached` above, and `Tc::view` runs the rewriter unless it is
// looking at a selection or at an `@` annotation.

/// The head of a description's weak head normal form, **with the value
/// discarded**: the levels are syntax in both domains, and the components a
/// rule descends into become new selections rather than spellings. This is
/// why nothing the checker keeps can outlive the arena.
pub(crate) enum ITyHead {
    Pi(Level, Level),
    Sigma(Level, Level),
    Sum(Level, Level),
    Other,
}

#[allow(clippy::too_many_arguments)]
pub(crate) fn conv_ity_cached(
    psi: &GlobalCtx,
    gamma: &LocalCtx,
    layer: Layer,
    a: &ITy,
    b: &ITy,
    level: &Level,
    fuel: u64,
    #[cfg(feature = "value-metrics")] metrics: Option<&ValueMetrics>,
    cache: Rc<GlobalCache>,
) -> R {
    debug_assert!(layer.computes(), "convertibility is only invoked at computing layers");
    #[cfg(feature = "value-metrics")]
    let arena = metrics.map_or_else(ValueArena::new, ValueArena::profiled);
    #[cfg(not(feature = "value-metrics"))]
    let arena = ValueArena::new();
    let env = Env::new_with(&arena, psi, gamma, layer, cache);
    Conv::<Values>::new(fuel, psi).ity_root(&env, a, b, level)
}

/// [`ITyHead`] of one description — `Tc::view`'s value-domain path.
#[allow(clippy::too_many_arguments)]
pub(crate) fn head_ity_cached(
    psi: &GlobalCtx,
    gamma: &LocalCtx,
    layer: Layer,
    t: &ITy,
    fuel: u64,
    #[cfg(feature = "value-metrics")] metrics: Option<&ValueMetrics>,
    cache: Rc<GlobalCache>,
) -> R<ITyHead> {
    debug_assert!(layer.computes(), "convertibility is only invoked at computing layers");
    #[cfg(feature = "value-metrics")]
    let arena = metrics.map_or_else(ValueArena::new, ValueArena::profiled);
    #[cfg(not(feature = "value-metrics"))]
    let arena = ValueArena::new();
    let env = Env::new_with(&arena, psi, gamma, layer, cache);
    let mut cv = Conv::<Values>::new(fuel, psi);
    let d = gamma.entries.len() as u32;
    let w = dom::values::eval_ity(&mut cv, &env, t, d, true)?;
    Ok(match &*w {
        VTy::Pi { dom_level, cod_level, .. } => {
            ITyHead::Pi(dom_level.clone(), cod_level.clone())
        }
        VTy::Sigma { fst_level, snd_level, .. } => {
            ITyHead::Sigma(fst_level.clone(), snd_level.clone())
        }
        VTy::Sum { lhs_level, rhs_level, .. } => {
            ITyHead::Sum(lhs_level.clone(), rhs_level.clone())
        }
        _ => ITyHead::Other,
    })
}


/// The **differential oracle**: conversion decided by the `reduce.rs` term
/// rewriter instead of by the value machine.
///
/// Not a checking API. Nothing in the kernel calls anything here, and
/// nothing outside a test should: the entry points above are conversion.
/// This module exists because the trusted-base story changed when the round
/// of `docs/nbe-conversion-design.md` landed — "ch. 06 verbatim" moved from
/// the algorithm to the *specification*, and `reduce.rs` is now the
/// specification. These functions are the same comparison arms instantiated
/// at [`dom::Syn`], so a test can run the two engines over one corpus and
/// require verdict-for-verdict agreement (`tests/conv_differential.rs`,
/// `tests/eval_differential.rs`). That standing evidence is one of the three
/// compensating controls the design doc §11.3 names; deleting it would
/// remove the only mechanical check that the machine still decides the
/// relation the paper states.
pub mod oracle {
    use super::*;

    /// [`super::conv_type`] decided by the rewriter.
    pub fn conv_type(
        psi: &GlobalCtx,
        gamma: &LocalCtx,
        layer: Layer,
        a: &Type,
        b: &Type,
        level: &Level,
        fuel: u64,
    ) -> R {
        debug_assert!(layer.computes(), "convertibility is only invoked at computing layers");
        let arena = ValueArena::new();
        Conv::<Syn>::new(fuel, psi).ty_root(&Env::new(&arena, psi, gamma, layer), a, b, level)
    }

    /// [`super::conv_term`] decided by the rewriter.
    #[allow(clippy::too_many_arguments)]
    pub fn conv_term(
        psi: &GlobalCtx,
        gamma: &LocalCtx,
        layer: Layer,
        a: &Term,
        b: &Term,
        ty: &Type,
        level: &Level,
        fuel: u64,
    ) -> R {
        debug_assert!(layer.computes(), "convertibility is only invoked at computing layers");
        let arena = ValueArena::new();
        Conv::<Syn>::new(fuel, psi).tm_root(&Env::new(&arena, psi, gamma, layer), a, b, ty, level)
    }

    /// [`super::conv_local_ctx`] decided by the rewriter.
    pub fn conv_local_ctx(
        psi: &GlobalCtx,
        layer: Layer,
        a: &LocalCtx,
        b: &LocalCtx,
        fuel: u64,
    ) -> R {
        debug_assert!(layer.computes(), "convertibility is only invoked at computing layers");
        let arena = ValueArena::new();
        let env = Env::new(&arena, psi, &LocalCtx::nil(), layer);
        Conv::<Syn>::new(fuel, psi).ctx(&env, layer, a, b)
    }
}

// ---------------------------------------------------------------------------
// Environment
// ---------------------------------------------------------------------------

/// The ambient scope of a comparison: Ψ, Γ, and the layer index. The
/// universe context L participates only by shifting (its length is never
/// consulted), so it is not tracked. Extending any namespace clones — the
/// judgments extend scopes freely and correctness beats performance here.
///
/// Γ is carried **twice**, and stage 2b's log says why. The syntactic
/// [`LocalCtx`] survives because three consumers read only its *length and
/// base* (`rec::branch_specs`, the shared `wf_step_telescope`, the identity
/// substitutions inside the syntax domain's [`Dom::inst_ty`]); at the value
/// domain its entry types are fillers. The scope a *value* needs — the
/// environment ρ of neutral variables, and each entry's type as a domain
/// object for [`Dom::var_type`] — is [`Env<'v>::rho`] and [`Env<'v>::vtys`], which
/// the syntax domain never reads.
#[derive(Clone)]
struct Env<'v> {
    /// Query-local storage for value closures and persistent environments.
    /// Kept here rather than in every compact value-domain `Env` handle.
    arena: &'v ValueArena<'v>,
    /// Shared, not cloned: a binder push clones the whole scope, and Ψ's
    /// bindings each carry a local context of their own — copying them per
    /// push was ~3% of a routine `lib/ir_v1.hthr` check. Only `push_tele`
    /// changes Ψ, and it is a layer-m path.
    psi: Rc<GlobalCtx>,
    /// Rescoped definition bodies and binding signatures for **this** Ψ
    /// (`reduce::GlobalCache`). Shared with every scope that shares the Ψ and
    /// rebuilt by the one operation that does not — `push_tele`.
    cache: Rc<GlobalCache>,
    /// Shared, not copied: a binder push clones the whole scope, and
    /// [`crate::term::CtxEntries`] is a spine, so extending Γ costs one cell
    /// and cloning this field costs a refcount bump. It was a `Vec`, and
    /// copying it per push was the #1 self line of a release
    /// `lib/ir_v1.hthr` check (issues/context-representation-clones.md).
    gamma: LocalCtx,
    layer: Layer,
    /// The local environment of the value domain: entry `j` from the outer
    /// end is the neutral variable at level `j`, so pushing a binder assigns
    /// the level `gamma.entries.len()` and never renumbers anything.
    rho: value::Env<'v>,
    /// The entry types of the binders **conversion itself pushed**, as domain
    /// objects, innermost first: those are the ones with no syntax in
    /// `gamma`. Everything older than `vbase` is still syntax there and is
    /// read back on demand, so entering a conversion costs no work per Γ
    /// entry (it cost O(|Γ|) allocations per query when this list was built
    /// eagerly — `scripts/bench`, 2026-07-31).
    vtys: TyEnv<'v>,
    /// The Γ-length at which `vtys` starts.
    vbase: u32,
    /// The telescope [`Dom::push_spec`] pushed to build this scope, as
    /// `(univs, globals, locals)`. Read by [`Dom::embed_ty_at`], which has to
    /// carry a recursor's stored environment across exactly that telescope.
    tele: (u32, u32, u32),
}

/// A persistent list of value-domain entry types: `Env<'v>` is cloned once per
/// binder push on conversion's hottest path, so this must not be a `Vec`.
#[derive(Clone)]
struct TyEnv<'v>(Option<Rc<TyEnvNode<'v>>>);

struct TyEnvNode<'v> {
    ty: &'v TyClo<'v>,
    level: Level,
    rest: TyEnv<'v>,
}

impl<'v> TyEnv<'v> {
    fn empty() -> TyEnv<'v> {
        TyEnv(None)
    }

    fn push(&self, ty: &'v TyClo<'v>, level: Level) -> TyEnv<'v> {
        TyEnv(Some(Rc::new(TyEnvNode { ty, level, rest: self.clone() })))
    }

    /// The entry `i` binders out from the innermost one.
    fn nth(&self, i: u32) -> Option<(&'v TyClo<'v>, &Level)> {
        let mut cur = self;
        let mut k = i;
        loop {
            let n = cur.0.as_ref()?;
            if k == 0 {
                return Some((n.ty, &n.level));
            }
            k -= 1;
            cur = &n.rest;
        }
    }

    /// Outermost first.
    fn to_vec(&self) -> Vec<(&'v TyClo<'v>, Level)> {
        let mut out = Vec::new();
        let mut cur = self;
        while let Some(n) = cur.0.as_ref() {
            out.push((n.ty, n.level.clone()));
            cur = &n.rest;
        }
        out.reverse();
        out
    }
}

/// The value-domain reading of a syntactic Γ: the identity environment of
/// its variables, and each entry's type as a closure over the *prefix* it is
/// scoped in.
fn value_scope<'v>(arena: &'v ValueArena<'v>, gamma: &LocalCtx) -> (value::Env<'v>, TyEnv<'v>) {
    (
        value::Env::identity(arena, gamma.entries.len() as u32),
        TyEnv::empty(),
    )
}

impl<'v> Env<'v> {
    fn new(
        arena: &'v ValueArena<'v>,
        psi: &GlobalCtx,
        gamma: &LocalCtx,
        layer: Layer,
    ) -> Env<'v> {
        Env::new_with(arena, psi, gamma, layer, Rc::new(GlobalCache::new()))
    }

    /// As [`Env::new`], but over a [`GlobalCache`] the caller keeps: the checker
    /// owns one per gate, so the rescoping survives the query that paid for it.
    fn new_with(
        arena: &'v ValueArena<'v>,
        psi: &GlobalCtx,
        gamma: &LocalCtx,
        layer: Layer,
        cache: Rc<GlobalCache>,
    ) -> Env<'v> {
        let (rho, vtys) = value_scope(arena, gamma);
        Env {
            arena,
            psi: Rc::new(psi.clone()),
            cache,
            gamma: gamma.clone(),
            layer,
            rho,
            vtys,
            vbase: gamma.entries.len() as u32,
            tele: (0, 0, 0),
        }
    }

    fn with_layer(&self, layer: Layer) -> Env<'v> {
        Env { layer, ..self.clone() }
    }

    /// Replace Γ (and the layer) — used where a rule compares inside a
    /// *different* local context, e.g. `Ψ; Δ ⊢_p T ≈ T'`. The value domain's
    /// scope is rebuilt from scratch: a different Γ is a different set of
    /// variables, at levels of its own.
    fn in_ctx(&self, gamma: LocalCtx, layer: Layer) -> Env<'v> {
        let (rho, vtys) = value_scope(self.arena, &gamma);
        let vbase = gamma.entries.len() as u32;
        Env { gamma, layer, rho, vtys, vbase, tele: (0, 0, 0), ..self.clone() }
    }

    /// `Γ, x : T @ l`. Reached through [`Dom::push_entry`], never directly:
    /// at the value domain pushing a binder also extends ρ with the binder's
    /// fresh neutral, and records the entry's type as a domain object.
    ///
    /// The syntactic entry is a **filler** unless the caller has real syntax
    /// (only [`Env<'v>::in_ctx`] and [`Env<'v>::new`] do): nothing reads it but the
    /// length and the base.
    fn push_entry_syn(&self, ty: Rc<Type>, level: Level) -> Env<'v> {
        let vty = self.arena.ty(TyClo::new(self.rho, Rc::clone(&ty)));
        self.push_entry(ty, vty, level)
    }

    fn push_entry(&self, ty: Rc<Type>, vty: &'v TyClo<'v>, level: Level) -> Env<'v> {
        let mut e = self.clone();
        let var = e.arena.tm(TmClo::val(Rc::new(value::Val::var(
            self.gamma.entries.len() as u32,
        ))));
        e.rho = e.rho.push(e.arena, var);
        e.vtys = e.vtys.push(vty, level.clone());
        e.gamma.entries.push(CtxEntry { ty, level });
        e
    }

    /// Push a telescope: `tu` universe binders then the given global
    /// bindings (each already scoped over `L, ℓ⃗` and its Ψ-prefix). The
    /// ambient Ψ and Γ are weakened accordingly — and so, at the value
    /// domain, is every value the scope carries (`value::shift`).
    fn push_tele(&self, tu: u32, globals: Vec<GlobalBinding>) -> Env<'v> {
        let tg = globals.len() as u32;
        let mut psi = shift_univ_psi(&self.psi, tu);
        psi.extend(globals);
        let psi = Rc::new(psi);
        let o = Outer { arena: self.arena, univs: tu, globals: tg };
        let mut vtys = TyEnv::empty();
        for (t, l) in self.vtys.to_vec() {
            vtys = vtys.push(value::shift::ty_clo(&t, o), l);
        }
        Env {
            arena: self.arena,
            psi,
            cache: Rc::new(GlobalCache::new()),
            gamma: self.gamma.shift_univ(tu).shift_global(tg),
            layer: self.layer,
            rho: value::shift::env(&self.rho, o),
            vtys,
            vbase: self.vbase,
            tele: (tu, tg, 0),
        }
    }

    fn push_univs(&self, n: u32) -> Env<'v> {
        self.push_tele(n, vec![])
    }

    fn push_global(&self, b: GlobalBinding) -> Env<'v> {
        self.push_tele(0, vec![b])
    }
}

/// Ψ-lookup: `bindings[len - 1 - v]` (0 is innermost). The result is scoped
/// over its *prefix* of Ψ — callers shift by `v + 1`.
fn lookup(psi: &GlobalCtx, v: GlobalVar) -> Option<&GlobalBinding> {
    psi.bindings.len().checked_sub(1 + v.0 as usize).and_then(|i| psi.bindings.get(i))
}

/// The **definition** at the head of a δ-stuck spine, if any: the one
/// global whose unfolding would let this term reduce further. Exactly the
/// scrutinee/head positions [`crate::reduce::is_neutral_term`] recurses
/// through, minus `transp`'s proof — that head belongs to [`Conv::strip`],
/// which runs after the δ-lazy stage.
fn delta_head(t: &Term, defs: Defs<'_>) -> Option<GlobalVar> {
    match t {
        Term::GlobalTm { var, .. } => defs.is_defined(*var).then_some(*var),
        Term::ElimNat { scrut, .. }
        | Term::ElimEmpty { scrut, .. }
        | Term::ElimSEmpty { scrut, .. }
        | Term::Case { scrut, .. }
        | Term::ElimW { scrut, .. }
        | Term::ElimWf { scrut, .. }
        | Term::LetBoxTy { scrut, .. }
        | Term::LetBoxTm { scrut, .. }
        | Term::ElimCodeTy { scrut, .. }
        | Term::ElimCodeTm { scrut, .. } => delta_head(scrut, defs),
        Term::J { proof, .. } => delta_head(proof, defs),
        Term::Fst { pair, .. }
        | Term::Snd { pair, .. }
        | Term::FstAt { pair }
        | Term::SndAt { pair } => delta_head(pair, defs),
        Term::App { fun, .. }
        | Term::AppAt { fun, .. }
        | Term::UApp { fun, .. }
        | Term::CtxApp { fun, .. }
        | Term::TyApp { fun, .. } => delta_head(fun, defs),
        _ => None,
    }
}

/// [`delta_head`] for types: a type is δ-stuck only under `El` (type-level
/// globals `U^δ` carry no body).
fn delta_head_ty(t: &Type, defs: Defs<'_>) -> Option<GlobalVar> {
    match t {
        Type::El { tm, .. } => delta_head(tm, defs),
        Type::Vec { len, .. } | Type::Fin { len } => delta_head(len, defs),
        _ => None,
    }
}

// ---------------------------------------------------------------------------
// The checker
// ---------------------------------------------------------------------------

/// Left side / right side of a recursor comparison (`C_A` inputs).
///
/// `motives` and `branches` are the only Γ-scoped **raw syntax** an
/// elimination carries, so they come with the scope they are read in
/// ([`Dom::RecCtx`]) rather than alone: at the value domain they agree with
/// the rewriter's rewritten copies only through the elimination's stored
/// environment.
struct RecSide<'a, 'v, D: Dom<'v>> {
    l1: &'a Level,
    l2: &'a Level,
    motives: Rc<Motives>,
    branches: Rc<Branches>,
    rec: D::RecCtx,
}

struct Conv<'v, D: Dom<'v>> {
    fuel: u64,
    /// Verdicts of [`Conv::tm`] already reached in this run, keyed by the
    /// two closures' identities ([`Dom::tm_memo_key`]). A closure denotes
    /// one term in one scope, and a well-typed term has one type up to
    /// conversion, so the verdict for a pair is a fact about the pair:
    /// convertible, or definitely not. Exhaustion is not a verdict and is
    /// never stored. It carries the repeated sub-comparisons a δ-lazy
    /// comparison makes of the same closures (loading the x86 model is
    /// ~30% slower without it); it cannot carry a lockstep unfolding, whose
    /// closures are fresh on every round — see the same-head arm of
    /// [`Conv::tm_w`] for that case.
    memo: HashMap<D::MemoKey, bool>,
    /// Does Ψ contain any definition at all? Decided once, because when it
    /// does not — every program before this feature, and every fixture that
    /// only declares — the δ-lazy stage below has nothing to find, and
    /// paying for it cost 1.35–1.43× on the conversion benchmarks. Telescope
    /// pushes never introduce definitions, so the answer cannot change while
    /// a comparison runs.
    has_defs: bool,
    /// Live native frames of [`Conv::tm`]/[`Conv::ty`], bounded by
    /// [`NATIVE_DEPTH_LIMIT`] and handed on to every evaluator run from
    /// inside them, so that one budget bounds the whole stack
    /// (docs/native-depth-budget-design.md).
    depth: u32,
    _dom: PhantomData<(&'v (), D)>,
}

impl<'v, D: Dom<'v>> Conv<'v, D> {
    fn new(fuel: u64, psi: &GlobalCtx) -> Conv<'v, D> {
        let has_defs = psi
            .bindings
            .iter()
            .any(|b| matches!(b, GlobalBinding::Tm { body: Some(_), .. }));
        Conv { fuel, has_defs, memo: HashMap::new(), depth: 0, _dom: PhantomData }
    }

    fn spend(&mut self) -> R {
        if self.fuel == 0 {
            return Err(ConvError::OutOfFuel);
        }
        self.fuel -= 1;
        Ok(())
    }

    /// Take one native frame of the depth budget; the caller gives it back
    /// with `self.depth -= 1` once its recursive call has returned. Paired by
    /// hand rather than by a guard type because the two comparison nodes are
    /// the only callers and a guard would borrow `self` across their bodies.
    fn descend(&mut self) -> R {
        if self.depth >= NATIVE_DEPTH_LIMIT {
            return Err(ConvError::OutOfFuel);
        }
        self.depth += 1;
        Ok(())
    }

    /// The δ-environment of a comparison: definitions unfold exactly at the
    /// computing layers (see [`Defs`]). Conversion is only ever invoked at
    /// p/m, so this is transparent in practice — the gate is here so that
    /// the one invariant that must never bend is stated where it is used,
    /// not assumed from the call sites.
    fn defs<'a>(&self, env: &'a Env<'v>) -> Defs<'a> {
        if self.has_defs && env.layer.computes() {
            Defs::transparent_cached(&env.psi, &env.cache)
        } else {
            Defs::opaque()
        }
    }

    /// The δ-lazy attempt: with both sides stuck at the *same* defined
    /// global head, try neutral-spine comparison first — `f a⃗ ≈ f a⃗`
    /// settles on the spine, and neither `f`'s body nor a type-directed η
    /// expansion is materialized. Failure means "unfold and retry", not
    /// "not convertible".
    ///
    /// Guard semantics are [`Conv::strip`]'s, for the same reason: catch
    /// `NotConvertible`, propagate `OutOfFuel` (the shared budget is spent
    /// and the verdict must not depend on *where* it died), and no fuel
    /// refund — monotone-decreasing fuel is the totality argument.
    fn delta_lazy<T>(&mut self, attempt: impl FnOnce(&mut Self) -> R<T>) -> R<Option<T>> {
        match attempt(self) {
            Ok(v) => Ok(Some(v)),
            Err(ConvError::NotConvertible) => Ok(None),
            Err(e) => Err(e),
        }
    }

    /// The **strip** loop: a stuck `transp(I; x.P; a; b; e; t)` whose
    /// endpoints convert is replaced by its payload `t`, re-whnf'd, and
    /// re-stripped — the equation `transp ≈ t` when `a ≈ b` (well-typed
    /// by `P[a] ≈ P[b]`), which covers what β cannot: a *neutral* proof
    /// at convertible endpoints (docs/sprop-design.md §5.2). The rule is
    /// keyed on the *term's* head, unlike the type-keyed η family, so it
    /// lives in the term-whnf stage of [`Conv::tm`] (which owns the
    /// hot-path discriminant check), not in a `tm_nf` type arm.
    ///
    /// The guard is an ordinary conversion query caught at this call
    /// site — not a query mode. `NotConvertible` means "keep the transp;
    /// the neutral path decides" and is the only caught error;
    /// `OutOfFuel` propagates (the shared budget is spent, and the
    /// verdict must not depend on *where* it died). No fuel refund on a
    /// failed guard: monotone-decreasing fuel is the totality argument
    /// (module doc). Each successful strip pays `spend()` — morally a
    /// conversion-level reduction step; the loop terminates because the
    /// payload is a strict subterm.
    #[cold]
    fn strip(&mut self, mut cur: D::Tm, env: &Env<'v>) -> R<D::Tm> {
        loop {
            if !D::is_transp(&cur) {
                return Ok(cur);
            }
            let (ty_level, ty, lhs, rhs, tm) = match D::view_tm(self, env, &cur) {
                TmView::Transp { ty_level, ty, lhs, rhs, tm, .. } => {
                    (ty_level.clone(), ty, lhs, rhs, tm)
                }
                _ => return Ok(cur),
            };
            // Fast path: syntactic endpoint equality (α-equality is free
            // under de Bruijn); the full guarded query — at the transp's
            // own annotations — only when that misses.
            let strip = D::tm_eq_fast(&lhs, &rhs)
                || match self.tm(env, &lhs, &rhs, &ty, &ty_level) {
                    Ok(()) => true,
                    Err(ConvError::NotConvertible) => false,
                    Err(e) => return Err(e),
                };
            if !strip {
                return Ok(cur);
            }
            self.spend()?;
            cur = D::whnf_tm(self, env, &tm)?;
        }
    }

    /// `L ⊢ l ≈ l' : Level` as a premise.
    fn lev_eq(&self, a: &Level, b: &Level) -> R {
        if a.equiv(b) { Ok(()) } else { Err(NC) }
    }

    // -- types --------------------------------------------------------------

    /// `Γ ⊢ T ≈ T' : l`: reduce both sides to WHNF, compare as normal.
    ///
    /// Reduction runs in two stages (extension,
    /// issues/simulate-conversion-cost.md): first without δ, and only if
    /// that leaves the two sides at different heads — or at the same
    /// defined head whose spines do not agree — with δ. A type reaches a
    /// definition only through `El ν`, so the head test is one hop deeper
    /// here than in [`Conv::tm`].
    fn ty(&mut self, env: &Env<'v>, a: &D::TyC, b: &D::TyC, l: &Level) -> R {
        self.spend()?;
        if D::ty_eq_fast(a, b) {
            return Ok(());
        }
        self.descend()?;
        let out = (|| {
            if let (Some((l1, e1, k1)), Some((l2, e2, k2))) =
                (D::vec_former(self, env, a), D::vec_former(self, env, b))
            {
                return self.vec_ty(env, &l1, &e1, &k1, &l2, &e2, &k2);
            }
            let mut wa = D::whnf_ty_opaque(self, env, a)?;
            let mut wb = D::whnf_ty_opaque(self, env, b)?;
            self.ty_w(env, &mut wa, &mut wb, l)
        })();
        self.depth -= 1;
        out
    }

    /// `Γ ⊢ Vec^l(T; k) ≈ Vec^l'(T'; k')` decided on the spelling, before
    /// either side reduces (extension; docs/wf-former-design.md §5).
    ///
    /// The verdict is the one the reductions give, reached without them.
    /// A vector at a canonical length *is* its right-nested `Σ` encoding,
    /// `Unit` at zero; so two vectors are convertible exactly when their
    /// lengths are and — unless that length is zero, where both are `Unit`
    /// whatever the element — their element types are. A canonical length
    /// against a neutral one never converts, and the encodings would not
    /// have either (`Σ` against a stuck `Vec`); two neutral lengths reach
    /// the same structural rule `ty_nf` applies to the neutral views. So no
    /// case falls through: the rule is total on two vector spellings, and
    /// nothing is retried on failure.
    ///
    /// What it saves is the shape: through the encodings the element type
    /// is compared once per `Σ` level, so a nested-pair literal of `n`
    /// elements — every level of which is annotated `Vec(T; k)` against the
    /// expected `Vec(T; k)` — cost `n²/2` element comparisons
    /// (`issues/elf-mutation-test-shape.md`); here it costs `n`.
    fn vec_ty(
        &mut self,
        env: &Env<'v>,
        l1: &Level,
        e1: &D::TyC,
        k1: &D::TmC,
        l2: &Level,
        e2: &D::TyC,
        k2: &D::TmC,
    ) -> R {
        self.lev_eq(l1, l2)?;
        self.tm_at_nat(env, k1, k2)?;
        let w = D::whnf_tm(self, env, k1)?;
        if matches!(D::view_tm(self, env, &w), TmView::Zero) {
            return Ok(());
        }
        self.ty(env, e1, e2, l1)
    }

    /// Unfold a δ-stuck **neutral** type until its head is a former or a
    /// spine no definition can advance — the type a comparison is *directed
    /// by* (the η arms, the neutral-application rule's Π) must expose its
    /// former, and one unfolding is not always enough: an alias of an alias,
    /// or an `El` of a code that a definition computes, stays neutral after
    /// one `delta_ty`. A former view (`Vec`, `Fin`, …) is left alone even
    /// when a *component* is δ-stuck: the view is already decisive there and
    /// forcing a length nobody reads would only spend fuel.
    /// Unfold a term's defined heads until none remains
    /// ([`Dom::delta_whnf_tm`]).
    fn delta_to_head_tm(&mut self, env: &Env<'v>, w: D::Tm) -> R<D::Tm> {
        if D::delta_head(self, env, &w).is_none() {
            return Ok(w);
        }
        D::delta_whnf_tm(self, env, w)
    }

    fn delta_to_head_ty(&mut self, env: &Env<'v>, mut w: D::Ty) -> R<D::Ty> {
        if self.has_defs {
            while D::view_ty(self, env, &w).is_neutral()
                && D::delta_head_ty(self, env, &w).is_some()
            {
                w = D::delta_ty(self, env, &w)?;
            }
        }
        Ok(w)
    }

    /// [`Conv::ty`] at the **root** of a conversion, where the two sides are
    /// raw syntax the caller lends us rather than sub-structures of a form
    /// already in the domain (see [`Dom::whnf_ty_root`]).
    ///
    /// Equal roots settle by **syntactic reflexivity**, not only object
    /// identity: α-equality is `==` under de Bruijn, `==`-equal level
    /// annotations are trivially `equiv`, and the typing seam's
    /// expected-vs-inferred query overwhelmingly hands this function two
    /// separately built copies of one type — on large canonical values the
    /// structural walk paid seconds where `==` pays microseconds
    /// (issues/conversion-cost-at-large-values.md). A failed `==` stops at
    /// the first difference, so its cost is bounded by a prefix of the walk
    /// the comparison performs anyway. Same fuel policy as every
    /// reflexivity shortcut: the hit spends this node's one unit.
    fn ty_root(&mut self, env: &Env<'v>, a: &Type, b: &Type, l: &Level) -> R {
        self.spend()?;
        if std::ptr::eq(a, b) || a == b {
            return Ok(());
        }
        let mut wa = D::whnf_ty_root(self, env, a)?;
        let mut wb = D::whnf_ty_root(self, env, b)?;
        self.ty_w(env, &mut wa, &mut wb, l)
    }

    /// The δ stage and the comparison, shared by the two entries above. The
    /// weak head forms are threaded by `&mut` and never by value: a `D::Ty`
    /// is a large enum at the syntax domain, and moving the two of them once
    /// more per node cost 1.28× on `nat/check-numeral`
    /// (`scripts/bench --check`, 2026-07-31).
    #[inline]
    fn ty_w(&mut self, env: &Env<'v>, wa: &mut D::Ty, wb: &mut D::Ty, l: &Level) -> R {
        if self.has_defs {
            loop {
                let heads =
                    (D::delta_head_ty(self, env, wa), D::delta_head_ty(self, env, wb));
                if let (Some(u1), Some(u2)) = heads
                    && u1 == u2
                    && self.delta_lazy(|c| c.ty_nf(env, wa, wb, l))?.is_some()
                {
                    return Ok(());
                }
                match heads {
                    (None, None) => break,
                    (Some(_), None) => *wa = D::delta_ty(self, env, wa)?,
                    (None, Some(_)) => *wb = D::delta_ty(self, env, wb)?,
                    (Some(u1), Some(u2)) if u1.0 < u2.0 => {
                        *wa = D::delta_ty(self, env, wa)?;
                    }
                    (Some(_), Some(_)) => {
                        *wb = D::delta_ty(self, env, wb)?;
                    }
                }
            }
        }
        self.ty_nf(env, wa, wb, l)
    }

    /// `Γ ⊢ W ≈ W' : l` for weak head normal types.
    fn ty_nf(&mut self, env: &Env<'v>, a: &D::Ty, b: &D::Ty, _l: &Level) -> R {
        let va = D::view_ty(self, env, a);
        let vb = D::view_ty(self, env, b);
        match (&va, &vb) {
            (TyView::Nat, TyView::Nat) => Ok(()),
            (TyView::Ty(x), TyView::Ty(y)) => self.lev_eq(x, y),
            (
                TyView::Pi { dom_level: dl1, cod_level: cl1, dom: s1, cod: t1 },
                TyView::Pi { dom_level: dl2, cod_level: cl2, dom: s2, cod: t2 },
            ) => {
                self.lev_eq(dl1, dl2)?;
                self.lev_eq(cl1, cl2)?;
                self.ty(env, s1, s2, dl1)?;
                let e = D::push_entry(env, s1, dl1);
                self.ty(&e, t1, t2, cl1)
            }
            // Id congruence (extension beyond ch. 04; kernel-v1-extensions).
            (
                TyView::Id { level: l1, ty: s1, lhs: t1, rhs: u1 },
                TyView::Id { level: l2, ty: s2, lhs: t2, rhs: u2 },
            ) => {
                self.lev_eq(l1, l2)?;
                self.ty(env, s1, s2, l1)?;
                self.tm(env, t1, t2, s1, l1)?;
                self.tm(env, u1, u2, s1, l1)
            }
            // sEq congruence (extension; docs/sprop-design.md §2.1) — Id's
            // arm verbatim. The *endpoints* are compared as ordinary terms;
            // only proofs (terms *at* sEq type) are irrelevant.
            (
                TyView::SEq { level: l1, ty: s1, lhs: t1, rhs: u1 },
                TyView::SEq { level: l2, ty: s2, lhs: t2, rhs: u2 },
            ) => {
                self.lev_eq(l1, l2)?;
                self.ty(env, s1, s2, l1)?;
                self.tm(env, t1, t2, s1, l1)?;
                self.tm(env, u1, u2, s1, l1)
            }
            (
                TyView::Squash { level: l1, ty: t1 },
                TyView::Squash { level: l2, ty: t2 },
            ) => {
                self.lev_eq(l1, l2)?;
                self.ty(env, t1, t2, l1)
            }
            // Σ congruence (extension; mirrors Π).
            (
                TyView::Sigma { fst_level: dl1, snd_level: cl1, fst: s1, snd: t1 },
                TyView::Sigma { fst_level: dl2, snd_level: cl2, fst: s2, snd: t2 },
            ) => {
                self.lev_eq(dl1, dl2)?;
                self.lev_eq(cl1, cl2)?;
                self.ty(env, s1, s2, dl1)?;
                let e = D::push_entry(env, s1, dl1);
                self.ty(&e, t1, t2, cl1)
            }
            // Unit^l / Empty^l / sEmpty^l congruence (extension): the formers
            // are level-indexed, so the levels must agree — up to `≈`, not
            // `==`.
            (TyView::Unit { level: l1 }, TyView::Unit { level: l2 })
            | (TyView::Empty { level: l1 }, TyView::Empty { level: l2 })
            | (TyView::SEmpty { level: l1 }, TyView::SEmpty { level: l2 }) => {
                self.lev_eq(l1, l2)
            }
            // Sum congruence (extension; non-dependent, so no binder push).
            (
                TyView::Sum { lhs_level: dl1, rhs_level: cl1, lhs: s1, rhs: t1 },
                TyView::Sum { lhs_level: dl2, rhs_level: cl2, lhs: s2, rhs: t2 },
            ) => {
                self.lev_eq(dl1, dl2)?;
                self.lev_eq(cl1, cl2)?;
                self.ty(env, s1, s2, dl1)?;
                self.ty(env, t1, t2, cl1)
            }
            // Vec/Fin congruence (extension): reached only at a *neutral*
            // length — a canonical one reduces away before `ty_nf` — so this
            // is the neutral-type comparison, structural in element and
            // length (docs/wf-former-design.md §5). Two sides both *spelled*
            // `Vec` are decided before reduction by [`Conv::vec_ty`]; this
            // arm is what remains when one side reached `Vec` by unfolding.
            (
                TyView::Vec { level: l1, elem: e1, len: k1 },
                TyView::Vec { level: l2, elem: e2, len: k2 },
            ) => {
                self.lev_eq(l1, l2)?;
                self.ty(env, e1, e2, l1)?;
                self.tm_at_nat(env, k1, k2)
            }
            (TyView::Fin { len: k1 }, TyView::Fin { len: k2 }) => {
                self.tm_at_nat(env, k1, k2)
            }
            // Wf congruence (extension): the arity is a Nat term under the
            // shape binder, so it is compared as a term in (Γ, x : S).
            (
                TyView::Wf { level: l1, shape: s1, arity: n1 },
                TyView::Wf { level: l2, shape: s2, arity: n2 },
            ) => {
                self.lev_eq(l1, l2)?;
                self.ty(env, s1, s2, l1)?;
                let e_x = D::push_entry(env, s1, l1);
                self.tm_at_nat(&e_x, n1, n2)
            }
            // W congruence (extension; mirrors Π/Σ).
            (
                TyView::W { shape_level: dl1, pos_level: cl1, shape: s1, pos: t1 },
                TyView::W { shape_level: dl2, pos_level: cl2, shape: s2, pos: t2 },
            ) => {
                self.lev_eq(dl1, dl2)?;
                self.lev_eq(cl1, cl2)?;
                self.ty(env, s1, s2, dl1)?;
                let e = D::push_entry(env, s1, dl1);
                self.ty(&e, t1, t2, cl1)
            }
            // -- layer-m type formers: mismatch outside layer m -------------
            (
                TyView::UPi { num_vars: n1, level: v1, body: b1 },
                TyView::UPi { num_vars: n2, level: v2, body: b2 },
            ) => {
                if env.layer != Layer::Meta || n1 != n2 {
                    return Err(NC);
                }
                self.lev_eq(v1, v2)?;
                let e = env.push_univs(*n1);
                // The bodies are *under* the pushed ℓ⃗; at the value domain
                // their captured environments are not, and have to be
                // weakened to match (design §3.1).
                let x = D::under_tele_ty(self, &e, b1, *n1, 0)?;
                let y = D::under_tele_ty(self, &e, b2, *n1, 0)?;
                self.ty(&e, &x, &y, v1)
            }
            (
                TyView::CtxPi { level: v1, body: b1 },
                TyView::CtxPi { level: v2, body: b2 },
            ) => {
                if env.layer != Layer::Meta {
                    return Err(NC);
                }
                self.lev_eq(v1, v2)?;
                let e = env.push_global(GlobalBinding::Ctx);
                let x = D::under_tele_ty(self, &e, b1, 0, 1)?;
                let y = D::under_tele_ty(self, &e, b2, 0, 1)?;
                self.ty(&e, &x, &y, v1)
            }
            (
                TyView::TyPi { ctx: c1, arg_level: a1, body_level: bl1, body: b1 },
                TyView::TyPi { ctx: c2, arg_level: a2, body_level: bl2, body: b2 },
            ) => {
                if env.layer != Layer::Meta {
                    return Err(NC);
                }
                self.lev_eq(a1, a2)?;
                self.lev_eq(bl1, bl2)?;
                self.ctx(env, Layer::Prog, c1, c2)?;
                let e = env.push_global(GlobalBinding::Ty {
                    ctx: (*c1).clone(),
                    layer: Layer::Prog,
                    level: (*a1).clone(),
                });
                let x = D::under_tele_ty(self, &e, b1, 0, 1)?;
                let y = D::under_tele_ty(self, &e, b2, 0, 1)?;
                self.ty(&e, &x, &y, bl1)
            }
            (
                TyView::CodeTy { ctx: c1, level: v1 },
                TyView::CodeTy { ctx: c2, level: v2 },
            ) => {
                if env.layer != Layer::Meta {
                    return Err(NC);
                }
                self.lev_eq(v1, v2)?;
                self.ctx(env, Layer::Prog, c1, c2)
            }
            (
                TyView::CodeTm { ctx: c1, ty: t1, level: v1 },
                TyView::CodeTm { ctx: c2, ty: t2, level: v2 },
            ) => {
                if env.layer != Layer::Meta {
                    return Err(NC);
                }
                self.lev_eq(v1, v2)?;
                self.ctx(env, Layer::Prog, c1, c2)?;
                let e = env.in_ctx((*c1).clone(), Layer::Prog);
                let (x, y) =
                    (D::embed_ty(&e, Rc::clone(t1)), D::embed_ty(&e, Rc::clone(t2)));
                self.ty(&e, &x, &y, v1)
            }
            // -- neutrals ---------------------------------------------------
            (x, y) if x.is_neutral() && y.is_neutral() => self.ty_ne(env, a, b).map(drop),
            _ => Err(NC),
        }
    }

    /// `Γ ⊢ V ≈ V' : l` for neutral types; the level is *inferred*
    /// (left-biased) and returned.
    fn ty_ne(&mut self, env: &Env<'v>, a: &D::Ty, b: &D::Ty) -> R<Level> {
        self.spend()?;
        let va = D::view_ty(self, env, a);
        let vb = D::view_ty(self, env, b);
        match (&va, &vb) {
            (
                TyView::GlobalTy { var: u1, subst: d1 },
                TyView::GlobalTy { var: u2, subst: d2 },
            ) => {
                if u1 != u2 {
                    return Err(NC);
                }
                let Some(GlobalBinding::Ty { ctx, layer, level }) = lookup(&env.psi, *u1)
                else {
                    return Err(NC);
                };
                // i' ∈ {c, p} is forced by the binding form; i' ≤ i:
                if *layer > env.layer {
                    return Err(NC);
                }
                let level = level.clone();
                crate::stats::global_ref_rescopes(1);
                let sig = env.cache.sig_or_insert(*u1, || Sig {
                    ctx: ctx.shift_global(u1.0 + 1),
                    ty: None,
                });
                self.subst(env, d1, d2, &sig.ctx)?;
                Ok(level)
            }
            (
                TyView::El { level: l1, tm: n1 },
                TyView::El { level: l2, tm: n2 },
            ) => {
                self.lev_eq(l1, l2)?;
                // inferred `Ty l`: redundant, ignored
                self.tm_nee_c(env, n1, n2)?;
                Ok((*l1).clone())
            }
            _ => Err(NC),
        }
    }

    // -- contexts and local substitutions -----------------------------------

    /// `⊢_i Γ ≈ Δ`, pairwise on entries (left-biased prefixes). `layer` is
    /// explicit because several rules compare index contexts at layer p.
    fn ctx(&mut self, env: &Env<'v>, layer: Layer, a: &LocalCtx, b: &LocalCtx) -> R {
        self.spend()?;
        if a == b {
            return Ok(());
        }
        if a.base != b.base || a.entries.len() != b.entries.len() {
            return Err(NC);
        }
        // The left prefix, grown as we go — see `Tc::ctx_wf` on why this is
        // not `a.prefix(k)` per entry.
        let mut prefix = LocalCtx { base: a.base, entries: CtxEntries::empty() };
        for (ea, eb) in a.entries.iter().zip(&b.entries) {
            let e = env.in_ctx(prefix.clone(), layer);
            let (x, y) = (
                D::embed_ty(&e, Rc::clone(&ea.ty)),
                D::embed_ty(&e, Rc::clone(&eb.ty)),
            );
            self.ty(&e, &x, &y, &ea.level)?;
            self.lev_eq(&ea.level, &eb.level)?;
            prefix = prefix.extended(Rc::clone(&ea.ty), ea.level.clone());
        }
        Ok(())
    }

    /// `Γ ⊢ δ ≈ δ' : Δ`, pairwise on the step terms over identical tails.
    fn subst(&mut self, env: &Env<'v>, d1: &D::Subst, d2: &D::Subst, target: &LocalCtx) -> R {
        self.spend()?;
        if !D::subst_tails_agree(d1, d2)
            || D::subst_len(d1) != target.entries.len()
            || D::subst_len(d2) != target.entries.len()
        {
            return Err(NC);
        }
        for (k, e) in target.entries.iter().enumerate() {
            let ty = D::apply_subst_ty(self, env, d1, k, &e.ty)?;
            let (x, y) = (D::subst_term(env, d1, k), D::subst_term(env, d2, k));
            self.tm(env, &x, &y, &ty, &e.level)?;
        }
        Ok(())
    }

    // -- terms --------------------------------------------------------------

    /// `Γ ⊢ t ≈ t' : T @ l`: reduce the type and both terms to WHNF, then
    /// compare type-directed.
    fn tm(&mut self, env: &Env<'v>, a: &D::TmC, b: &D::TmC, ty: &D::TyC, l: &Level) -> R {
        self.spend()?;
        if D::tm_identity_fast(a, b) {
            return Ok(());
        }
        let key = D::tm_memo_key(env, a, b);
        if let Some(key) = &key {
            if let Some(&verdict) = self.memo.get(key) {
                return if verdict { Ok(()) } else { Err(ConvError::NotConvertible) };
            }
        }
        self.descend()?;
        let result = (|| {
            let w = D::whnf_ty(self, env, ty)?;
            let wa = D::whnf_tm_opaque(self, env, a)?;
            let wb = D::whnf_tm_opaque(self, env, b)?;
            self.tm_w(env, wa, wb, &w, l)
        })();
        self.depth -= 1;
        if let Some(key) = key {
            match &result {
                Ok(()) => {
                    self.memo.insert(key, true);
                }
                Err(ConvError::NotConvertible) => {
                    self.memo.insert(key, false);
                }
                Err(ConvError::OutOfFuel) => {}
            }
        }
        result
    }

    /// [`Conv::tm`] at the **root**; see [`Conv::ty_root`].
    fn tm_root(&mut self, env: &Env<'v>, a: &Term, b: &Term, ty: &Type, l: &Level) -> R {
        self.spend()?;
        let w = D::whnf_ty_root(self, env, ty)?;
        let wa = D::whnf_tm_root(self, env, a)?;
        let wb = D::whnf_tm_root(self, env, b)?;
        self.tm_w(env, wa, wb, &w, l)
    }

    /// The δ stage, the transp strip and the comparison, shared by the two
    /// entries above.
    #[inline]
    fn tm_w(&mut self, env: &Env<'v>, mut wa: D::Tm, mut wb: D::Tm, w: &D::Ty, l: &Level) -> R {
        // δ-lazy stage (extension; see [`Conv::ty`]): stop at a definition's
        // spine, and when both sides stop at the *same* one, try the spine
        // comparison before unfolding anything.
        // whnf, then strip transp heads whose endpoints convert
        // ([`Conv::strip`]). The check is inline (not a whnf-wrapping
        // helper) so the hot path — no transp head, i.e. every pre-sEq
        // program — pays one discriminant read and zero extra `Term`
        // moves; the helper layering cost 1.35× on `conv/computed-numeral`
        // (`scripts/bench --check`, 2026-07-28).
        if self.has_defs {
            loop {
                let heads = (D::delta_head(self, env, &wa), D::delta_head(self, env, &wb));
                if let (Some(u1), Some(u2)) = heads
                    && u1 == u2
                    // A defined head is neutral even when its declared result
                    // is a positive type. Compare that neutral spine directly:
                    // routing through `tm_nf` would invoke type-directed η
                    // first (for example, projecting every field of a
                    // `BitVec`) and needlessly force the definition body.
                    && self.delta_lazy(|c| c.tm_nee(env, &wa, &wb).map(drop))?.is_some()
                {
                    return Ok(());
                }
                match heads {
                    (None, None) => break,
                    // The other side has no defined head, so no rendezvous
                    // at one is possible and this side unfolds until it
                    // has none either — the sequence of single steps the
                    // loop would otherwise take, done as one transparent
                    // reduction (`Dom::delta_whnf_tm`) so that a spine
                    // stuck on a glued scrutinee is not replayed per step.
                    (Some(_), None) => wa = self.delta_to_head_tm(env, wa)?,
                    (None, Some(_)) => wb = self.delta_to_head_tm(env, wb)?,
                    // A body can mention only older globals. With de Bruijn
                    // global indices, the newer declaration has the smaller
                    // index in the current Ψ. Advance only that side: if it
                    // is a transparent wrapper around the other head, the
                    // next loop iteration meets there instead of unfolding
                    // the other side past the rendezvous in lockstep.
                    (Some(u1), Some(u2)) if u1.0 < u2.0 => {
                        wa = D::delta_tm(self, env, &wa)?;
                    }
                    // The same head on both sides, and the meet there just
                    // failed. Two reactions, keyed on what the head *is* to
                    // each side.
                    //
                    // Bare applications `f a⃗` and `f b⃗`: the failure says
                    // `a⃗ ≉ b⃗`, so this head is spent. Advancing one side a
                    // single step and re-comparing would re-evaluate the
                    // body it exposes on every round — with every closure
                    // beneath it fresh each time, so nothing below is ever
                    // shared or memoized — and two `ofNat(8, k)` at
                    // different `k` exhausted 2^20 units that way. Nothing
                    // is lost by unfolding both sides to their δ-heads
                    // instead: a meet at a sub-term is still found by the
                    // ordinary lazy comparison of the canonical forms'
                    // components.
                    //
                    // Eliminations stuck on glued scrutinees, `E₁[f a⃗]` and
                    // `E₂[f b⃗]`: the shared head is only what the two
                    // scrutinees happen to compute with, and the failure
                    // may be `E₁`'s against `E₂`'s — `match class_of(x)`
                    // against `match cont_of(y)` share `bit7` — which says
                    // nothing about where the *terms* would meet. Normalizing
                    // both here throws that meet away and unrolls whatever
                    // the bodies hide: `utf8::decode` at a three-byte
                    // sequence against its own `decode_seq` went through
                    // `nat::leb(0x800, code)` at a stuck `code`, a 2048-deep
                    // closure chain on each side that no comparison can
                    // descend (`issues/utf8-decode-conversion-blowup.md`).
                    // So each side takes one δ-step and the loop looks for
                    // the next meet — the same lockstep the different-head
                    // arms take, with both sides moving because neither is
                    // the newer.
                    (Some(u1), Some(u2)) if u1 == u2 => {
                        if D::is_application_spine(&wa) && D::is_application_spine(&wb) {
                            wa = self.delta_to_head_tm(env, wa)?;
                            wb = self.delta_to_head_tm(env, wb)?;
                        } else {
                            wa = D::delta_tm(self, env, &wa)?;
                            wb = D::delta_tm(self, env, &wb)?;
                        }
                    }
                    (Some(_), Some(_)) => {
                        wb = D::delta_tm(self, env, &wb)?;
                    }
                }
            }
        }
        if D::is_transp(&wa) {
            wa = self.strip(wa, env)?;
        }
        if D::is_transp(&wb) {
            wb = self.strip(wb, env)?;
        }
        // A δ-stuck **type** unfolds before the comparison is directed by it
        // — the mirror of [`Conv::ty_w`]'s δ stage, which until 2026-08-13
        // terms never had: `tm` whnfs its type opaquely, so two canonical
        // values at `El (u^δ)` for a *defined* `u` fell into the
        // neutral-type arm and compared as neutrals — `NotConvertible` for
        // any literal, even two identical ones. Unreachable while defined
        // codes never stood in annotation slots; `El (D#tycode^δ)` in an
        // `Id`'s type component (family-code design §10, the component
        // respell) is checked by exactly this comparison. The same-head
        // fast path above is unaffected: it compares spines at the stuck
        // type, where both sides are neutral and `tm_nee` is the right
        // judge.
        if self.has_defs && D::delta_head_ty(self, env, w).is_some() {
            let w = D::delta_ty(self, env, w)?;
            let w = self.delta_to_head_ty(env, w)?;
            return self.tm_nf(env, &wa, &wb, &w, l);
        }
        self.tm_nf(env, &wa, &wb, w, l)
    }

    /// `Γ ⊢ k ≈ k' : Nat @ 0` — the length/arity comparison the `Vec`, `Fin`
    /// and `Wf` families all make.
    fn tm_at_nat(&mut self, env: &Env<'v>, a: &D::TmC, b: &D::TmC) -> R {
        self.tm(env, a, b, &D::nat(env), &Level::Zero)
    }

    /// `Γ ⊢ s ≈ s' : Ty l @ l+1` — two type *encodings*.
    fn tm_at_univ(&mut self, env: &Env<'v>, a: &D::TmC, b: &D::TmC, l: &Level) -> R {
        let univ = D::univ(env, l);
        self.tm(env, a, b, &univ, &Level::succ(l.clone()))
    }

    /// `Γ, x : El^l s` — the binder every dependent encoding pushes.
    fn push_el(&mut self, env: &Env<'v>, l: &Level, s: &D::TmC) -> R<Env<'v>> {
        let el = D::el(self, env, l, s)?;
        Ok(D::push_entry(env, &el, l))
    }

    /// `Γ ⊢ w ≈ w' : W @ l` for weak head normal terms at a WHNF type,
    /// directed by the type.
    fn tm_nf(&mut self, env: &Env<'v>, a: &D::Tm, b: &D::Tm, w: &D::Ty, _l: &Level) -> R {
        let vw = D::view_ty(self, env, w);
        match &vw {
            // η: Γ, x : S ⊢ app(w↑; l,l'; x:S↑.T↑; x) ≈ app(w'↑; …; x) : T
            TyView::Pi { dom_level, cod_level, dom, cod } => {
                let e = D::push_entry(env, dom, dom_level);
                let (x, y) =
                    D::eta_app(self, env, &e, a, b, dom_level, cod_level, dom, cod)?;
                self.tm(&e, &x, &y, cod, cod_level)
            }
            // η: L, ℓ⃗ ⊢ w↑ $ ℓ⃗ ≈ w'↑ $ ℓ⃗ : T
            TyView::UPi { num_vars, level, body } => {
                if env.layer != Layer::Meta {
                    return Err(NC);
                }
                let e = env.push_univs(*num_vars);
                let (x, y) = D::eta_uapp(self, env, &e, a, b, *num_vars)?;
                let t = D::under_tele_ty(self, &e, body, *num_vars, 0)?;
                self.tm(&e, &x, &y, &t, level)
            }
            // η: Ψ, g : Ctx ⊢ w↑ @ g ≈ w'↑ @ g : T
            TyView::CtxPi { level, body } => {
                if env.layer != Layer::Meta {
                    return Err(NC);
                }
                let e = env.push_global(GlobalBinding::Ctx);
                let (x, y) = D::eta_ctxapp(self, env, &e, a, b)?;
                let t = D::under_tele_ty(self, &e, body, 0, 1)?;
                self.tm(&e, &x, &y, &t, level)
            }
            // η: Ψ, U : Typ_p(Δ, l) ⊢ w↑ @ U^{id_Δ} ≈ w'↑ @ U^{id_Δ} : T
            TyView::TyPi { ctx, arg_level, body_level, body } => {
                if env.layer != Layer::Meta {
                    return Err(NC);
                }
                let e = env.push_global(GlobalBinding::Ty {
                    ctx: (*ctx).clone(),
                    layer: Layer::Prog,
                    level: (*arg_level).clone(),
                });
                let (x, y) = D::eta_tyapp(self, env, &e, a, b, ctx)?;
                let t = D::under_tele_ty(self, &e, body, 0, 1)?;
                self.tm(&e, &x, &y, &t, body_level)
            }
            // Code compares syntactically — *modulo level equivalence*, which
            // is the quotient ch. 05's Static Code lemma (`lem:dt:static`)
            // takes: at layers v/c equivalence is equality, "quotient over
            // the equivalence of universe levels", and the paper's own
            // example is that `Ty (ℓ ⊔ ℓ')` and `Ty (ℓ' ⊔ ℓ)` are equal *as
            // code*. Plain `==` here would reject that pair — incompleteness
            // against ch. 08's Convertibility theorem, not unsoundness, but a
            // spurious error for any universe-polymorphic metaprogram.
            // Neutrals still compare structurally.
            TyView::CodeTy { .. } => match (&D::view_tm(self, env, a), &D::view_tm(self, env, b)) {
                (TmView::BoxTy(t1), TmView::BoxTy(t2)) => {
                    if code_eq(&***t1, &***t2) { Ok(()) } else { Err(NC) }
                }
                (TmView::BoxTy(_), _) | (_, TmView::BoxTy(_)) => Err(NC),
                _ => self.tm_nee(env, a, b).map(drop),
            },
            TyView::CodeTm { .. } => match (&D::view_tm(self, env, a), &D::view_tm(self, env, b)) {
                (TmView::BoxTm(t1), TmView::BoxTm(t2)) => {
                    if code_eq(&***t1, &***t2) { Ok(()) } else { Err(NC) }
                }
                (TmView::BoxTm(_), _) | (_, TmView::BoxTm(_)) => Err(NC),
                _ => self.tm_nee(env, a, b).map(drop),
            },
            TyView::Nat => {
                if let Some((x, y)) = D::cancel_nat_prefix(self, env, a, b)? {
                    return self.tm_at_nat(env, &x, &y);
                }
                match (&D::view_tm(self, env, a), &D::view_tm(self, env, b)) {
                    (TmView::Zero, TmView::Zero) => Ok(()),
                    (TmView::Succ(x), TmView::Succ(y)) => self.tm_at_nat(env, x, y),
                    (x, y) if x.is_nat_data() || y.is_nat_data() => Err(NC),
                    _ => self.tm_nee(env, a, b).map(drop),
                }
            }
            TyView::Ty(_) => match (&D::view_tm(self, env, a), &D::view_tm(self, env, b)) {
                (TmView::TmNat, TmView::TmNat) => Ok(()),
                (TmView::TmTy(x), TmView::TmTy(y)) => self.lev_eq(x, y),
                (
                    TmView::TmPi { dom_level: dl1, cod_level: cl1, dom: s1, cod: t1 },
                    TmView::TmPi { dom_level: dl2, cod_level: cl2, dom: s2, cod: t2 },
                ) => {
                    self.lev_eq(dl1, dl2)?;
                    self.lev_eq(cl1, cl2)?;
                    self.tm_at_univ(env, s1, s2, dl1)?;
                    let e = self.push_el(env, dl1, s1)?;
                    self.tm_at_univ(&e, t1, t2, cl1)
                }
                // TmId congruence (extension).
                (
                    TmView::TmId { level: l1, ty: s1, lhs: t1, rhs: u1 },
                    TmView::TmId { level: l2, ty: s2, lhs: t2, rhs: u2 },
                ) => {
                    self.lev_eq(l1, l2)?;
                    self.tm_at_univ(env, s1, s2, l1)?;
                    let el = D::el(self, env, l1, s1)?;
                    self.tm(env, t1, t2, &el, l1)?;
                    self.tm(env, u1, u2, &el, l1)
                }
                // TmSEq congruence (extension; mirrors TmId — the
                // *encoding* compares structurally like any code; only
                // terms AT sEq type are irrelevant).
                (
                    TmView::TmSEq { level: l1, ty: s1, lhs: t1, rhs: u1 },
                    TmView::TmSEq { level: l2, ty: s2, lhs: t2, rhs: u2 },
                ) => {
                    self.lev_eq(l1, l2)?;
                    self.tm_at_univ(env, s1, s2, l1)?;
                    let el = D::el(self, env, l1, s1)?;
                    self.tm(env, t1, t2, &el, l1)?;
                    self.tm(env, u1, u2, &el, l1)
                }
                (
                    TmView::TmSquash { level: l1, ty: t1 },
                    TmView::TmSquash { level: l2, ty: t2 },
                ) => {
                    self.lev_eq(l1, l2)?;
                    self.tm_at_univ(env, t1, t2, l1)
                }
                // TmSigma congruence (extension; mirrors TmPi).
                (
                    TmView::TmSigma { fst_level: dl1, snd_level: cl1, fst: s1, snd: t1 },
                    TmView::TmSigma { fst_level: dl2, snd_level: cl2, fst: s2, snd: t2 },
                ) => {
                    self.lev_eq(dl1, dl2)?;
                    self.lev_eq(cl1, cl2)?;
                    self.tm_at_univ(env, s1, s2, dl1)?;
                    let e = self.push_el(env, dl1, s1)?;
                    self.tm_at_univ(&e, t1, t2, cl1)
                }
                // TmUnit/TmEmpty/TmsEmpty congruence (extension; nullary
                // encodings).
                (TmView::TmUnit { level: l1 }, TmView::TmUnit { level: l2 })
                | (TmView::TmEmpty { level: l1 }, TmView::TmEmpty { level: l2 })
                | (TmView::TmSEmpty { level: l1 }, TmView::TmSEmpty { level: l2 }) => {
                    self.lev_eq(l1, l2)
                }
                // TmSum congruence (extension; non-dependent, mirrors TmSigma).
                (
                    TmView::TmSum { lhs_level: dl1, rhs_level: cl1, lhs: s1, rhs: t1 },
                    TmView::TmSum { lhs_level: dl2, rhs_level: cl2, lhs: s2, rhs: t2 },
                ) => {
                    self.lev_eq(dl1, dl2)?;
                    self.lev_eq(cl1, cl2)?;
                    self.tm_at_univ(env, s1, s2, dl1)?;
                    self.tm_at_univ(env, t1, t2, cl1)
                }
                // TmW congruence (extension; mirrors TmPi/TmSigma).
                (
                    TmView::TmW { shape_level: dl1, pos_level: cl1, shape: s1, pos: t1 },
                    TmView::TmW { shape_level: dl2, pos_level: cl2, shape: s2, pos: t2 },
                ) => {
                    self.lev_eq(dl1, dl2)?;
                    self.lev_eq(cl1, cl2)?;
                    self.tm_at_univ(env, s1, s2, dl1)?;
                    let e = self.push_el(env, dl1, s1)?;
                    self.tm_at_univ(&e, t1, t2, cl1)
                }
                // TmVec/TmFin congruence (extension): the length is compared
                // at Nat in the ambient scope — no binder, unlike TmWf.
                (
                    TmView::TmVec { level: l1, elem: s1, len: k1 },
                    TmView::TmVec { level: l2, elem: s2, len: k2 },
                ) => {
                    self.lev_eq(l1, l2)?;
                    self.tm_at_univ(env, s1, s2, l1)?;
                    self.tm_at_nat(env, k1, k2)
                }
                (TmView::TmFin { len: k1 }, TmView::TmFin { len: k2 }) => {
                    self.tm_at_nat(env, k1, k2)
                }
                // TmWf congruence (extension): the arity is compared at Nat
                // under the shape binder, mirroring TmW's positions.
                (
                    TmView::TmWf { level: l1, shape: s1, arity: n1 },
                    TmView::TmWf { level: l2, shape: s2, arity: n2 },
                ) => {
                    self.lev_eq(l1, l2)?;
                    self.tm_at_univ(env, s1, s2, l1)?;
                    let e = self.push_el(env, l1, s1)?;
                    self.tm_at_nat(&e, n1, n2)
                }
                (x, y) if x.is_encoding() || y.is_encoding() => Err(NC),
                _ => self.tm_nee(env, a, b).map(drop),
            },
            // Id (extension): refl congruence on the point; else neutral.
            // The refl annotations are forced by well-typedness at this Id
            // type, so only the point is compared.
            TyView::Id { level, ty, .. } => match (&D::view_tm(self, env, a), &D::view_tm(self, env, b))
            {
                (TmView::Refl { tm: x }, TmView::Refl { tm: y }) => {
                    self.tm(env, x, y, ty, level)
                }
                (TmView::Refl { .. }, _) | (_, TmView::Refl { .. }) => Err(NC),
                _ => self.tm_nee(env, a, b).map(drop),
            },
            // Σ η (extension): surjective pairing — type-directed like the Π
            // η arm, so it fires on literal pairs, neutrals, or mixtures.
            // Compare `fst a ≈ fst b : S` and `snd a ≈ snd b : T[fst a/x]`.
            TyView::Sigma { fst_level, snd_level, fst, snd } => {
                // Native bitvector words (extension;
                // `docs/native-bitvector-values-design.md` §7), ahead of the
                // guard below and for the same observation carried one step
                // further: a `Vec` is a right-nested Σ, and when its element
                // type has exactly two canonical inhabitants the whole chain
                // is a machine word. Comparing two *canonical* 64-bit
                // vectors component by component costs ~59 evaluator steps
                // per bit before any operation has been performed at all
                // (the design's §2 A3 floor); packing performs the same
                // projections η would have performed and then compares in
                // one instruction. Anything that does not pack falls through
                // to η unchanged.
                if D::bit_vec_eq(self, env, a, b, fst, snd, snd_level)?.is_some() {
                    return Ok(());
                }
                // Neutral-first (extension): two stuck terms whose spines
                // agree are convertible by congruence, and deciding that on
                // the spines costs the spines. Projecting first instead
                // costs the *type*: a `Vec` is a right-nested Σ, so η on two
                // neutral 64-bit vectors compares 64 components, each a
                // `fst (snd^k …)` whose own neutral comparison walks its k
                // projections — quadratic in the length, and a machine word
                // is the common case. A failed attempt falls through to η,
                // which is what decides the η-equal-but-not-spine-equal
                // pairs; the guard semantics are [`Conv::delta_lazy`]'s.
                if D::view_tm(self, env, a).is_neutral()
                    && D::view_tm(self, env, b).is_neutral()
                    && self.delta_lazy(|c| c.tm_nee(env, a, b).map(drop))?.is_some()
                {
                    return Ok(());
                }
                let (fa, fb) =
                    D::eta_proj(self, env, true, a, b, fst_level, snd_level, fst, snd)?;
                self.tm(env, &fa, &fb, fst, fst_level)?;
                let snd_ty = D::inst_ty(self, env, env, snd, &[fa])?;
                let (sa, sb) =
                    D::eta_proj(self, env, false, a, b, fst_level, snd_level, fst, snd)?;
                self.tm(env, &sa, &sb, &snd_ty, snd_level)
            }
            // Unit η (extension): proof irrelevance — every term of Unit type
            // is convertible to ⟨⟩, hence to each other. Type-directed like Σ
            // η, so it fires on ⟨⟩, neutrals, or mixtures without inspecting
            // either side.
            TyView::Unit { .. } => Ok(()),
            // sEq irrelevance (extension; docs/sprop-design.md §5.2): the
            // Unit pattern generalized — any two proofs of a strict equality
            // are definitionally equal. This arm is also what lets the
            // transp congruence in `tm_ne` skip the proofs, and what makes
            // UIP at sEq definitional (`p ≡ srefl`) rather than a theorem.
            // Both of Unit's ch. 07 §4 consequences apply verbatim:
            // presupposition holds by assumption on the caller, and the arm
            // must sit here in `tm_nf`, ahead of any structural fallback.
            TyView::SEq { .. } => Ok(()),
            // sEmpty irrelevance (extension; docs/sprop-design.md §2.2):
            // unlike Empty (structural neutrals, below), any two absurdity
            // proofs are convertible — vacuously sound, the type is
            // uninhabited in consistent contexts.
            TyView::SEmpty { .. } => Ok(()),
            // Propositional truncation is definitionally proof-irrelevant,
            // while evaluation above still forces both sides to WHNF.
            TyView::Squash { .. } => Ok(()),
            // Empty (extension): no canonical inhabitants, so only neutrals can
            // appear; compare them structurally.
            TyView::Empty { .. } => self.tm_nee(env, a, b).map(drop),
            // Sum (extension): a positive type — the two constructors match
            // like `Zero`/`Succ` at `Nat`. The annotations on inl/inr are
            // forced by well-typedness at this sum type, so only the injected
            // value is compared; a tag mismatch is `NotConvertible`; neutrals
            // (a stuck `case`, a variable) fall through to structural
            // comparison.
            TyView::Sum { lhs_level, rhs_level, lhs, rhs } => {
                match (&D::view_tm(self, env, a), &D::view_tm(self, env, b)) {
                    (TmView::Inl { val: x }, TmView::Inl { val: y }) => {
                        self.tm(env, x, y, lhs, lhs_level)
                    }
                    (TmView::Inr { val: x }, TmView::Inr { val: y }) => {
                        self.tm(env, x, y, rhs, rhs_level)
                    }
                    (TmView::Inl { .. } | TmView::Inr { .. }, _)
                    | (_, TmView::Inl { .. } | TmView::Inr { .. }) => Err(NC),
                    _ => self.tm_nee(env, a, b).map(drop),
                }
            }
            // W (extension): a positive type — `sup` matches like the sum
            // constructors. The annotations on sup are forced by
            // well-typedness at this W type, so only the label and the
            // subtree function are compared (the latter at the left label's
            // instantiated Π type, left-biased); neutrals (a stuck elim_W, a
            // variable) fall through to structural comparison.
            TyView::W { shape_level, pos_level, shape, pos } => {
                match (&D::view_tm(self, env, a), &D::view_tm(self, env, b)) {
                    (
                        TmView::Sup { label: a1, children: f1 },
                        TmView::Sup { label: a2, children: f2 },
                    ) => {
                        self.tm(env, a1, a2, shape, shape_level)?;
                        let lmax = Level::max((*shape_level).clone(), (*pos_level).clone());
                        let pos_at = D::inst_ty(self, env, env, pos, std::slice::from_ref(a1))?;
                        let w_c = D::as_child_ty(self, env, w)?;
                        let cod = D::weaken_ty(env, &w_c, 1);
                        let f_ty = D::pi(self, env, pos_level, &lmax, &pos_at, &cod)?;
                        let f_l = Level::max((*pos_level).clone(), lmax);
                        self.tm(env, f1, f2, &f_ty, &f_l)
                    }
                    (TmView::Sup { .. }, _) | (_, TmView::Sup { .. }) => Err(NC),
                    _ => self.tm_nee(env, a, b).map(drop),
                }
            }
            // Wf (extension): positive, like W — but the children compare at
            // a `Vec`, so the comparison descends through `Σ`-η and bottoms
            // out in `Unit`'s proof irrelevance. That is the whole reason
            // this former exists (docs/wf-former-design.md §5): no funext is
            // reachable from here, because there is no function to compare.
            TyView::Wf { level, shape, arity } => {
                match (&D::view_tm(self, env, a), &D::view_tm(self, env, b)) {
                    (
                        TmView::Supf { label: a1, children: c1 },
                        TmView::Supf { label: a2, children: c2 },
                    ) => {
                        self.tm(env, a1, a2, shape, level)?;
                        // Children at Vec(Wf; n[a₁/x]), left-biased like W's.
                        let arity_at = D::inst_tm(self, env, env, arity, std::slice::from_ref(a1))?;
                        let w_c = D::as_child_ty(self, env, w)?;
                        let cs_ty = D::vec(self, env, level, &w_c, &arity_at)?;
                        self.tm(env, c1, c2, &cs_ty, level)
                    }
                    (TmView::Supf { .. }, _) | (_, TmView::Supf { .. }) => Err(NC),
                    _ => self.tm_nee(env, a, b).map(drop),
                }
            }
            // Neutral type: only neutral terms inhabit it. `Vec`/`Fin` reach
            // here only at a neutral length (a canonical one reduces to
            // Σ/Unit resp. Sum/Empty first, and those arms then supply the
            // η) — so they behave exactly like the other neutral types.
            TyView::El { .. }
            | TyView::GlobalTy { .. }
            | TyView::Vec { .. }
            | TyView::Fin { .. } => self.tm_nee(env, a, b).map(drop),
        }
    }

    /// Neutral comparison with the inferred type reduced to WHNF.
    fn tm_nee(&mut self, env: &Env<'v>, a: &D::Tm, b: &D::Tm) -> R<(D::Ty, Level)> {
        let (t, l) = self.tm_ne(env, a, b)?;
        let w = D::whnf_ty(self, env, &t)?;
        Ok((w, l))
    }

    /// [`Conv::tm_nee`] on two *sub-structures* — an eliminator's scrutinee,
    /// an application's function. They are already in weak head normal form
    /// (the form carrying them is), so reaching their heads is a no-op at the
    /// syntax domain and a `force` at the value domain.
    fn tm_nee_c(&mut self, env: &Env<'v>, a: &D::TmC, b: &D::TmC) -> R<(D::Ty, Level)> {
        let x = D::head_tm(self, env, a)?;
        let y = D::head_tm(self, env, b)?;
        self.tm_nee(env, &x, &y)
    }

    /// `Γ ⊢ ν ≈ ν' : T @ l` for neutral terms; the type and level are
    /// *inferred* (left-biased) and returned. Layer-m elimination forms
    /// bump the ambient layer to m — their rules are stated there, and the
    /// layer index restricts only types.
    fn tm_ne(&mut self, env: &Env<'v>, a: &D::Tm, b: &D::Tm) -> R<(D::TyC, Level)> {
        self.spend()?;
        let va = D::view_tm(self, env, a);
        let vb = D::view_tm(self, env, b);
        match (&va, &vb) {
            (TmView::Var(x), TmView::Var(y)) => {
                if x != y {
                    return Err(NC);
                }
                D::var_type(self, env, *x)
            }
            (
                TmView::GlobalTm { var: u1, subst: d1 },
                TmView::GlobalTm { var: u2, subst: d2 },
            ) => {
                if u1 != u2 {
                    return Err(NC);
                }
                let Some(GlobalBinding::Tm { ctx, layer, ty, level, .. }) =
                    lookup(&env.psi, *u1)
                else {
                    return Err(NC);
                };
                // i' ∈ {v, c} is forced by the binding form; i' ≤ i:
                if *layer > env.layer {
                    return Err(NC);
                }
                let level = level.clone();
                crate::stats::global_ref_rescopes(1);
                let sig = env.cache.sig_or_insert(*u1, || Sig {
                    ctx: ctx.shift_global(u1.0 + 1),
                    ty: Some(Rc::new(ty.shift_global(u1.0 + 1))),
                });
                // The binding form fixes the kind at this index, so a `Tm`
                // lookup always finds the `Tm` signature; the guard is a
                // kernel that reports rather than panics on a broken Ψ.
                let Some(ty) = sig.ty.as_ref() else { return Err(NC) };
                self.subst(env, d1, d2, &sig.ctx)?;
                let n = D::subst_len(d1);
                Ok((D::apply_subst_ty(self, env, d1, n, ty)?, level))
            }
            (
                TmView::ElimNat { level: v1, motive: m1, base: z1, step: s1, scrut: n1 },
                TmView::ElimNat { level: v2, motive: m2, base: z2, step: s2, scrut: n2 },
            ) => {
                self.lev_eq(v1, v2)?;
                let e_x = D::push_entry(env, &D::nat(env), &Level::Zero);
                self.ty(&e_x, m1, m2, v1)?;
                let base_ty = D::inst_ty(self, env, env, m1, &[D::zero(env)])?;
                self.tm(env, z1, z2, &base_ty, v1)?;
                // M[su x/x] scoped in (Γ, x : Nat, y : M), as in reduce.rs.
                let e_xy = D::push_entry(&e_x, m1, v1);
                let x1 = D::local(&e_xy, LocalVar(1));
                let su_x = D::succ(self, &e_xy, &x1)?;
                let step_ty = D::inst_ty(self, env, &e_xy, m1, std::slice::from_ref(&su_x))?;
                self.tm(&e_xy, s1, s2, &step_ty, v1)?;
                self.tm_nee_c(env, n1, n2)?; // inferred Nat: redundant, ignored
                Ok((D::inst_ty(self, env, env, m1, std::slice::from_ref(n1))?, (*v1).clone()))
            }
            // elim_Empty neutral congruence (extension); mirrors ElimNat
            // minus the base/step branches.
            (
                TmView::ElimEmpty { level: v1, scrut_level: s1, motive: m1, scrut: n1 },
                TmView::ElimEmpty { level: v2, scrut_level: s2, motive: m2, scrut: n2 },
            ) => {
                self.lev_eq(v1, v2)?;
                self.lev_eq(s1, s2)?;
                let em = D::empty(env, s1);
                let e_x = D::push_entry(env, &em, s1);
                self.ty(&e_x, m1, m2, v1)?;
                self.tm_nee_c(env, n1, n2)?; // inferred Empty: redundant, ignored
                Ok((D::inst_ty(self, env, env, m1, std::slice::from_ref(n1))?, (*v1).clone()))
            }
            // elim_sEmpty neutral congruence (extension) — ElimEmpty's arm
            // with the scrutinees *skipped*: they sit at sEmpty, whose
            // irrelevance arm accepts any two terms, so comparing them
            // would be that arm anyway (docs/sprop-design.md §5.3). The
            // motive instances agree for the same reason.
            (
                TmView::ElimSEmpty { level: v1, scrut_level: s1, motive: m1, scrut: n1 },
                TmView::ElimSEmpty { level: v2, scrut_level: s2, motive: m2, scrut: _ },
            ) => {
                self.lev_eq(v1, v2)?;
                self.lev_eq(s1, s2)?;
                let em = D::sempty(env, s1);
                let e_x = D::push_entry(env, &em, s1);
                self.ty(&e_x, m1, m2, v1)?;
                Ok((D::inst_ty(self, env, env, m1, std::slice::from_ref(n1))?, (*v1).clone()))
            }
            (
                TmView::ElimSquash {
                    src_level: s1,
                    dst_level: d1,
                    src_ty: a1,
                    motive: m1,
                    scrut: n1,
                },
                TmView::ElimSquash {
                    src_level: s2,
                    dst_level: d2,
                    src_ty: a2,
                    motive: m2,
                    scrut: _,
                },
            ) => {
                self.lev_eq(s1, s2)?;
                self.lev_eq(d1, d2)?;
                self.ty(env, a1, a2, s1)?;
                let sq_a = D::squash(env, s1, a1);
                let e_z = D::push_entry(env, &sq_a, s1);
                self.ty(&e_z, m1, m2, d1)?;
                let inner = D::inst_ty(self, &e_z, env, m1, std::slice::from_ref(n1))?;
                Ok((D::squash(env, d1, &inner), (*d1).clone()))
            }
            // case neutral congruence (extension); mirrors ElimNat — all
            // annotations compared (branches at M[inl x/z] / M[inr y/z]), the
            // scrutinee via tm_nee, result inferred as M[scrut/z]. Fires only
            // on a neutral scrutinee (canonical inl/inr β-fired in reduce).
            (
                TmView::Case {
                    lhs_level: dl1,
                    rhs_level: cl1,
                    motive_level: ml1,
                    lhs: s1,
                    rhs: t1,
                    motive: m1,
                    case_l: l1,
                    case_r: r1,
                    scrut: n1,
                },
                TmView::Case {
                    lhs_level: dl2,
                    rhs_level: cl2,
                    motive_level: ml2,
                    lhs: s2,
                    rhs: t2,
                    motive: m2,
                    case_l: l2,
                    case_r: r2,
                    scrut: n2,
                },
            ) => {
                self.lev_eq(dl1, dl2)?;
                self.lev_eq(cl1, cl2)?;
                self.lev_eq(ml1, ml2)?;
                self.ty(env, s1, s2, dl1)?;
                self.ty(env, t1, t2, cl1)?;
                let lmax = Level::max((*dl1).clone(), (*cl1).clone());
                let sum = D::sum(self, env, dl1, cl1, s1, t1)?;
                // M scoped in (Γ, z : A + B), as in typing.rs.
                let e_z = D::push_entry(env, &sum, &lmax);
                self.ty(&e_z, m1, m2, ml1)?;
                let s1_up = D::weaken_ty(env, s1, 1);
                let t1_up = D::weaken_ty(env, t1, 1);
                // c_l at M[inl x/z] in (Γ, x : A).
                let e_x = D::push_entry(env, s1, dl1);
                let x0 = D::local(&e_x, LocalVar(0));
                let inl_x =
                    D::inj(self, &e_x, true, dl1, cl1, &s1_up, &t1_up, &x0)?;
                let left_ty = D::inst_ty(self, env, &e_x, m1, std::slice::from_ref(&inl_x))?;
                self.tm(&e_x, l1, l2, &left_ty, ml1)?;
                // c_r at M[inr y/z] in (Γ, y : B).
                let e_y = D::push_entry(env, t1, cl1);
                let y0 = D::local(&e_y, LocalVar(0));
                let inr_y =
                    D::inj(self, &e_y, false, dl1, cl1, &s1_up, &t1_up, &y0)?;
                let right_ty = D::inst_ty(self, env, &e_y, m1, std::slice::from_ref(&inr_y))?;
                self.tm(&e_y, r1, r2, &right_ty, ml1)?;
                self.tm_nee_c(env, n1, n2)?; // inferred A + B: redundant, ignored
                Ok((D::inst_ty(self, env, env, m1, std::slice::from_ref(n1))?, (*ml1).clone()))
            }
            // elim_W neutral congruence (extension); mirrors ElimNat/Case —
            // all annotations compared (the step at M[sup(a,f)/z] under the
            // (a, f, ih) telescope, as in typing.rs), the scrutinee via
            // tm_nee, result inferred as M[scrut/z]. Fires only on a neutral
            // scrutinee (a canonical sup β-fired in reduce).
            (
                TmView::ElimW {
                    shape_level: dl1,
                    pos_level: cl1,
                    motive_level: ml1,
                    shape: s1,
                    pos: t1,
                    motive: m1,
                    step: st1,
                    scrut: n1,
                },
                TmView::ElimW {
                    shape_level: dl2,
                    pos_level: cl2,
                    motive_level: ml2,
                    shape: s2,
                    pos: t2,
                    motive: m2,
                    step: st2,
                    scrut: n2,
                },
            ) => {
                self.lev_eq(dl1, dl2)?;
                self.lev_eq(cl1, cl2)?;
                self.lev_eq(ml1, ml2)?;
                self.ty(env, s1, s2, dl1)?;
                let e_x = D::push_entry(env, s1, dl1);
                self.ty(&e_x, t1, t2, cl1)?;
                let lmax = Level::max((*dl1).clone(), (*cl1).clone());
                let w_ty = D::w(self, env, dl1, cl1, s1, t1)?;
                // M scoped in (Γ, z : W).
                let e_z = D::push_entry(env, &w_ty, &lmax);
                self.ty(&e_z, m1, m2, ml1)?;
                // Steps under (Γ, a : S, f : Π(y:T[a/x]). W,
                // ih : Π(y:T[a/x]). M[f y/z]) at M[sup(a, f)/z] — the same
                // construction as the typing rule.
                let e_a = D::push_entry(env, s1, dl1);
                let a_var = D::local(&e_a, LocalVar(0));
                // T[a/x] in (Γ, a): the positions are a *body* under the
                // shape binder, so this is instantiation, not weakening.
                let t_at_a = D::inst_ty(self, env, &e_a, t1, &[a_var])?;
                let f_ty =
                    D::pi(self, &e_a, cl1, &lmax, &t_at_a, &D::weaken_ty(&e_a, &w_ty, 2))?;
                let e_af =
                    D::push_entry(&e_a, &f_ty, &Level::max((*cl1).clone(), lmax.clone()));
                let a_var2 = D::local(&e_af, LocalVar(1));
                let t_at_a_af = D::inst_ty(self, env, &e_af, t1, &[a_var2])?;
                let e_afy = D::push_entry(&e_af, &t_at_a_af, cl1);
                let a_var3 = D::local(&e_afy, LocalVar(2));
                let t_at_a_afy = D::inst_ty(self, env, &e_afy, t1, &[a_var3])?;
                let f_y = D::app(
                    self,
                    &e_afy,
                    cl1,
                    &lmax,
                    &t_at_a_afy,
                    &D::weaken_ty(&e_afy, &w_ty, 4),
                    &D::local(&e_afy, LocalVar(1)),
                    &D::local(&e_afy, LocalVar(0)),
                )?;
                let ih_cod = D::inst_ty(self, env, &e_afy, m1, std::slice::from_ref(&f_y))?;
                let ih_ty = D::pi(self, &e_af, cl1, ml1, &t_at_a_af, &ih_cod)?;
                let e_step =
                    D::push_entry(&e_af, &ih_ty, &Level::max((*cl1).clone(), (*ml1).clone()));
                let sup_af = D::sup_at(
                    self,
                    &e_af,
                    &w_ty,
                    2,
                    &D::local(&e_af, LocalVar(1)),
                    &D::local(&e_af, LocalVar(0)),
                )?;
                let step_ty =
                    D::inst_ty(self, env, &e_step, m1, &[D::weaken_tm(&e_step, &sup_af, 1)])?;
                self.tm(&e_step, st1, st2, &step_ty, ml1)?;
                self.tm_nee_c(env, n1, n2)?; // inferred W: redundant, ignored
                Ok((D::inst_ty(self, env, env, m1, std::slice::from_ref(n1))?, (*ml1).clone()))
            }
            // elim_Wf neutral congruence (extension): same shape as elim_W's,
            // with the step telescope taken from `wf_step_telescope` — the
            // single source shared with typing.rs, so the two cannot drift.
            // Fires only on a neutral scrutinee; this is what makes two
            // inductions over the *same* open term convertible.
            (
                TmView::ElimWf {
                    level: l1,
                    motive_level: ml1,
                    shape: s1,
                    arity: k1,
                    motive: m1,
                    step: st1,
                    scrut: n1,
                },
                TmView::ElimWf {
                    level: l2,
                    motive_level: ml2,
                    shape: s2,
                    arity: k2,
                    motive: m2,
                    step: st2,
                    scrut: n2,
                },
            ) => {
                self.lev_eq(l1, l2)?;
                self.lev_eq(ml1, ml2)?;
                self.ty(env, s1, s2, l1)?;
                let e_x = D::push_entry(env, s1, l1);
                self.tm_at_nat(&e_x, k1, k2)?;
                let wf = D::wf(self, env, l1, s1, k1)?;
                let e_z = D::push_entry(env, &wf, l1);
                self.ty(&e_z, m1, m2, ml1)?;
                let (cs_ty, ih_ty, step_ty) =
                    D::wf_step_telescope(self, env, l1, ml1, s1, k1, m1)?;
                let e_a = D::push_entry(env, s1, l1);
                let e_cs = D::push_entry(&e_a, &cs_ty, l1);
                let e_step = D::push_entry(&e_cs, &ih_ty, ml1);
                self.tm(&e_step, st1, st2, &step_ty, ml1)?;
                self.tm_nee_c(env, n1, n2)?; // inferred Wf: redundant, ignored
                Ok((D::inst_ty(self, env, env, m1, std::slice::from_ref(n1))?, (*ml1).clone()))
            }
            // J neutral congruence (extension beyond ch. 04); mirrors the
            // ElimNat arm — annotations compared, scrutinee via tm_nee.
            (
                TmView::J {
                    ty_level: al1,
                    motive_level: ml1,
                    ty: s1,
                    lhs: a1,
                    motive: m1,
                    case: c1,
                    rhs: r1,
                    proof: p1,
                },
                TmView::J {
                    ty_level: al2,
                    motive_level: ml2,
                    ty: s2,
                    lhs: a2,
                    motive: m2,
                    case: c2,
                    rhs: r2,
                    proof: p2,
                },
            ) => {
                self.lev_eq(al1, al2)?;
                self.lev_eq(ml1, ml2)?;
                self.ty(env, s1, s2, al1)?;
                self.tm(env, a1, a2, s1, al1)?;
                // M scoped in (Γ, y : S, p : Id^l(S; a; y)), as in typing.rs.
                let e_y = D::push_entry(env, s1, al1);
                let p_ty = D::id(
                    self,
                    &e_y,
                    al1,
                    &D::weaken_ty(&e_y, s1, 1),
                    &D::weaken_tm(&e_y, a1, 1),
                    &D::local(&e_y, LocalVar(0)),
                )?;
                let e_yp = D::push_entry(&e_y, &p_ty, al1);
                self.ty(&e_yp, m1, m2, ml1)?;
                let refl_a = D::refl(self, env, al1, s1, a1)?;
                let case_ty = D::inst_ty(self, env, env, m1, &[a1.clone(), refl_a])?;
                self.tm(env, c1, c2, &case_ty, ml1)?;
                self.tm(env, r1, r2, s1, al1)?;
                self.tm_nee_c(env, p1, p2)?; // inferred Id: redundant, ignored
                Ok((D::inst_ty(self, env, env, m1, &[r1.clone(), p1.clone()])?, (*ml1).clone()))
            }
            // transp congruence (extension; docs/sprop-design.md §5.3) —
            // reached only when *both* sides' strip guards failed, i.e. two
            // genuinely stuck transports. Inverts J's discipline: J compares
            // its proof structurally because the proof is its scrutinee and
            // neutrality is keyed on it; transp's stuckness is keyed on the
            // endpoints, so two stuck transps over *different* neutral
            // proofs must still be equal — the proofs are deliberately not
            // compared (their type is sEq, whose irrelevance arm accepts any
            // two terms; skipping is that arm applied, not a special case).
            (
                TmView::Transp {
                    ty_level: al1,
                    motive_level: ml1,
                    ty: s1,
                    motive: m1,
                    lhs: a1,
                    rhs: b1,
                    tm: t1,
                },
                TmView::Transp {
                    ty_level: al2,
                    motive_level: ml2,
                    ty: s2,
                    motive: m2,
                    lhs: a2,
                    rhs: b2,
                    tm: t2,
                },
            ) => {
                self.lev_eq(al1, al2)?;
                self.lev_eq(ml1, ml2)?;
                self.ty(env, s1, s2, al1)?;
                self.tm(env, a1, a2, s1, al1)?;
                self.tm(env, b1, b2, s1, al1)?;
                // P scoped in (Γ, x : I), as in typing.rs.
                let e_x = D::push_entry(env, s1, al1);
                self.ty(&e_x, m1, m2, ml1)?;
                let t_ty = D::inst_ty(self, env, env, m1, std::slice::from_ref(a1))?;
                self.tm(env, t1, t2, &t_ty, ml1)?;
                Ok((D::inst_ty(self, env, env, m1, std::slice::from_ref(b1))?, (*ml1).clone()))
            }
            (
                TmView::App { levels: ls1, fun: f1, arg: a1 },
                TmView::App { levels: ls2, fun: f2, arg: a2 },
            ) => {
                // Levels as the `Fst` arm below: compared when both sides
                // store them, and otherwise the inferred Π's are the answer
                // (`app@`, docs/app-by-head-type-design.md §4).
                if let (Some((dl1, cl1)), Some((dl2, cl2))) = (ls1, ls2) {
                    self.lev_eq(dl1, dl2)?;
                    self.lev_eq(cl1, cl2)?;
                }
                // Typed application rule (extension; the mirror image of the
                // ch. 06 note below its application rule). The paper compares
                // the two stored `x:S.T` annotations and *ignores* the type
                // inferred for the heads, "because we already know ν and ν'
                // are well-typed so the type annotations must be
                // equivalent". That well-typedness runs the other way just
                // as well: each annotation converts with the Π inferred for
                // its own head, the heads convert, and convertible neutrals
                // infer convertible types (ch. 08) — so relating the two
                // annotations to each other adds nothing on the well-typed
                // inputs conversion presupposes. What it *costs* is the
                // whole per-node price of a spine: at every application node
                // the codomain annotation is the entire remaining Π, whose
                // domains are themselves neutral applications with their own
                // annotations, so one n-ary spine compared n annotation
                // suffixes and recursed into each — the `ty_nf`/`ty_w` stacks
                // and the tens of millions of type closures of
                // issues/application-annotation-sharing-cost.md.
                //
                // So: compare the heads, read the Π they infer, compare the
                // arguments at *its* domain and return *its* codomain. The
                // inferred type is fully δ-reduced ([`Conv::tm_nee`]) and
                // then driven to its head ([`Conv::delta_to_head_ty`]) —
                // the 2026-08-27 attempt viewed it as it came, which is what
                // refused the dependent fold/tabulate instances
                // (issues/generated-term-oracle-controls-not-convertible.md).
                // The stored annotations are ignored here exactly as the
                // inferred type was before; the typing seam still checks
                // every annotation against its head's type once, at the
                // term's own check.
                let (w, _) = self.tm_nee_c(env, f1, f2)?;
                let w = self.delta_to_head_ty(env, w)?;
                let TyView::Pi { dom_level, cod_level, dom, cod } = D::view_ty(self, env, &w)
                else {
                    return Err(NC);
                };
                let (dom_level, cod_level) = (dom_level.clone(), cod_level.clone());
                self.tm(env, a1, a2, &dom, &dom_level)?;
                Ok((D::inst_ty(self, env, env, &cod, std::slice::from_ref(a1))?, cod_level))
            }
            // fst/snd neutral congruence (extension; mirrors App — typed, at
            // the Σ inferred for the pair). These arms fire only when the
            // projected pair is itself neutral (η already handled non-neutral
            // pairs in tm_nf).
            (
                TmView::Fst { levels: ls1, pair: p1 },
                TmView::Fst { levels: ls2, pair: p2 },
            ) => {
                // Both stored: the redundant cross-check the component
                // spelling affords. Either side a checked spelling: no
                // stored levels to compare, and the inferred Σ below is the
                // answer either way.
                if let (Some((dl1, cl1)), Some((dl2, cl2))) = (ls1, ls2) {
                    self.lev_eq(dl1, dl2)?;
                    self.lev_eq(cl1, cl2)?;
                }
                // Typed projection rule — the App arm's argument, verbatim:
                // on well-typed inputs each stored Σ annotation converts with
                // the Σ inferred for its own pair, so relating the two
                // annotations to each other adds nothing, and costs the size
                // of the remaining tuple type at *every* node of a projection
                // chain (a Wf record's children tuple is exactly such a chain,
                // and its annotations carry the whole shape).
                let (w, _) = self.tm_nee_c(env, p1, p2)?;
                let w = self.delta_to_head_ty(env, w)?;
                let TyView::Sigma { fst_level, fst, .. } = D::view_ty(self, env, &w) else {
                    return Err(NC);
                };
                Ok((fst, fst_level.clone()))
            }
            (
                TmView::Snd { levels: ls1, pair: p1 },
                TmView::Snd { levels: ls2, pair: p2 },
            ) => {
                if let (Some((dl1, cl1)), Some((dl2, cl2))) = (ls1, ls2) {
                    self.lev_eq(dl1, dl2)?;
                    self.lev_eq(cl1, cl2)?;
                }
                // As for `fst`: the inferred Σ, not the stored annotations.
                let (w, _) = self.tm_nee_c(env, p1, p2)?;
                let w = self.delta_to_head_ty(env, w)?;
                let TyView::Sigma { fst_level, snd_level, fst, snd } = D::view_ty(self, env, &w)
                else {
                    return Err(NC);
                };
                let (fst_level, snd_level) = (fst_level.clone(), snd_level.clone());
                let fst_p = D::proj(self, env, true, &fst_level, &snd_level, &fst, &snd, p1)?;
                Ok((D::inst_ty(self, env, env, &snd, std::slice::from_ref(&fst_p))?, snd_level))
            }
            (
                TmView::UApp { levels: ls1, fun: f1 },
                TmView::UApp { levels: ls2, fun: f2 },
            ) => {
                let env = &env.with_layer(Layer::Meta);
                let (w, _) = self.tm_nee_c(env, f1, f2)?;
                let TyView::UPi { num_vars, level, body } = D::view_ty(self, env, &w) else {
                    return Err(NC);
                };
                if ls1.len() != ls2.len() || ls1.len() != num_vars as usize || ls1.is_empty()
                {
                    return Err(NC);
                }
                for (x, y) in ls1.iter().zip(*ls2) {
                    self.lev_eq(x, y)?;
                }
                // Written vectors are outermost-first; instantiation wants
                // innermost-first (as in reduce.rs).
                let phi: Vec<Level> = ls1.iter().rev().cloned().collect();
                let l = level.inst_at(&phi, 0);
                Ok((D::inst_univ_ty(self, env, &body, &phi)?, l))
            }
            (
                TmView::CtxApp { ctx: c1, fun: f1 },
                TmView::CtxApp { ctx: c2, fun: f2 },
            ) => {
                let env = &env.with_layer(Layer::Meta);
                let (w, _) = self.tm_nee_c(env, f1, f2)?;
                let TyView::CtxPi { level, body } = D::view_ty(self, env, &w) else {
                    return Err(NC);
                };
                let level = level.clone();
                self.ctx(env, Layer::Prog, c1, c2)?;
                Ok((D::inst_ctx_ty(self, env, &body, c1)?, level))
            }
            (
                TmView::TyApp { arg: t1, fun: f1 },
                TmView::TyApp { arg: t2, fun: f2 },
            ) => {
                let env = &env.with_layer(Layer::Meta);
                let (w, _) = self.tm_nee_c(env, f1, f2)?;
                let TyView::TyPi { ctx, arg_level, body_level, body } = D::view_ty(self, env, &w)
                else {
                    return Err(NC);
                };
                let body_level = body_level.clone();
                let e_d = env.in_ctx(ctx.clone(), Layer::Prog);
                let (x, y) =
                    (D::embed_ty(&e_d, Rc::clone(t1)), D::embed_ty(&e_d, Rc::clone(t2)));
                self.ty(&e_d, &x, &y, arg_level)?;
                Ok((D::inst_tyarg_ty(self, env, &body, t1)?, body_level))
            }
            (
                TmView::LetBoxTy {
                    motive_level: ml1,
                    code_level: cl1,
                    ctx: d1,
                    motive: m1,
                    body: b1,
                    scrut: n1,
                },
                TmView::LetBoxTy {
                    motive_level: ml2,
                    code_level: cl2,
                    ctx: d2,
                    motive: m2,
                    body: b2,
                    scrut: n2,
                },
            ) => {
                let env = &env.with_layer(Layer::Meta);
                self.lev_eq(ml1, ml2)?;
                self.lev_eq(cl1, cl2)?;
                self.ctx(env, Layer::Prog, d1, d2)?;
                self.tm_nee_c(env, n1, n2)?; // inferred □(Δ ⊢ Ty l): ignored
                let code_ty = D::code_ty(env, d1, cl1);
                let e_x = D::push_entry(env, &code_ty, &Level::Zero);
                self.ty(&e_x, m1, m2, ml1)?;
                // Bodies under Ψ, U : Typ_c(Δ, l) at M[box U/x_T].
                let e_u = env.push_global(GlobalBinding::Ty {
                    ctx: (*d1).clone(),
                    layer: Layer::Code,
                    level: (*cl1).clone(),
                });
                let box_u = D::box_ty(&e_u, Rc::new(gty(0, &d1.shift_global(1))));
                let m_u = D::shift_global_ty(self, &e_u, m1, 1)?;
                let body_ty = D::inst_ty(self, &e_u, &e_u, &m_u, std::slice::from_ref(&box_u))?;
                // The bodies are under `Ψ, U`; their captured scopes are not.
                let x = D::under_tele_tm(self, &e_u, b1, 0, 1)?;
                let y = D::under_tele_tm(self, &e_u, b2, 0, 1)?;
                self.tm(&e_u, &x, &y, &body_ty, ml1)?;
                Ok((D::inst_ty(self, env, env, m1, std::slice::from_ref(n1))?, (*ml1).clone()))
            }
            (
                TmView::LetBoxTm {
                    motive_level: ml1,
                    code_level: cl1,
                    ctx: d1,
                    ty: t1,
                    motive: m1,
                    body: b1,
                    scrut: n1,
                },
                TmView::LetBoxTm {
                    motive_level: ml2,
                    code_level: cl2,
                    ctx: d2,
                    ty: t2,
                    motive: m2,
                    body: b2,
                    scrut: n2,
                },
            ) => {
                let env = &env.with_layer(Layer::Meta);
                self.lev_eq(ml1, ml2)?;
                self.lev_eq(cl1, cl2)?;
                self.ctx(env, Layer::Prog, d1, d2)?;
                let e_d = env.in_ctx((*d1).clone(), Layer::Prog);
                let (x, y) =
                    (D::embed_ty(&e_d, Rc::clone(t1)), D::embed_ty(&e_d, Rc::clone(t2)));
                self.ty(&e_d, &x, &y, cl1)?;
                self.tm_nee_c(env, n1, n2)?; // inferred □(Δ ⊢ T @ l): ignored
                let code_ty = D::code_tm(env, d1, t1, cl1);
                let e_x = D::push_entry(env, &code_ty, &Level::Zero);
                self.ty(&e_x, m1, m2, ml1)?;
                // Bodies under Ψ, u : Trm_c(Δ ⊢ T @ l) at M[box u/x_t].
                let e_u = env.push_global(GlobalBinding::Tm {
                    ctx: (*d1).clone(),
                    layer: Layer::Code,
                    ty: Rc::clone(t1),
                    level: (*cl1).clone(),
                    body: None,
                });
                let box_u = D::box_tm(&e_u, Rc::new(gtm(0, &d1.shift_global(1))));
                let m_u = D::shift_global_ty(self, &e_u, m1, 1)?;
                let body_ty = D::inst_ty(self, &e_u, &e_u, &m_u, std::slice::from_ref(&box_u))?;
                let x = D::under_tele_tm(self, &e_u, b1, 0, 1)?;
                let y = D::under_tele_tm(self, &e_u, b2, 0, 1)?;
                self.tm(&e_u, &x, &y, &body_ty, ml1)?;
                Ok((D::inst_ty(self, env, env, m1, std::slice::from_ref(n1))?, (*ml1).clone()))
            }
            (
                TmView::ElimCodeTy {
                    ty_motive_level: al1,
                    tm_motive_level: al2,
                    motives: am,
                    branches: ab,
                    code_level: acl,
                    ctx: actx,
                    scrut: an,
                    rec: arec,
                },
                TmView::ElimCodeTy {
                    ty_motive_level: bl1,
                    tm_motive_level: bl2,
                    motives: bm,
                    branches: bb,
                    code_level: bcl,
                    ctx: bctx,
                    scrut: bn,
                    rec: brec,
                },
            ) => {
                let env = &env.with_layer(Layer::Meta);
                self.rec_ca(
                    env,
                    &RecSide {
                        l1: al1,
                        l2: al2,
                        motives: Rc::clone(am),
                        branches: Rc::clone(ab),
                        rec: arec.clone(),
                    },
                    &RecSide {
                        l1: bl1,
                        l2: bl2,
                        motives: Rc::clone(bm),
                        branches: Rc::clone(bb),
                        rec: brec.clone(),
                    },
                )?;
                self.lev_eq(acl, bcl)?;
                self.ctx(env, Layer::Prog, actx, bctx)?;
                // Blocked on box (U^δ): compared syntactically. Otherwise the
                // scrutinees are neutral.
                match (
                    D::box_ty_payload(self, env, an)?,
                    D::box_ty_payload(self, env, bn)?,
                ) {
                    (Some(c1), Some(c2)) => match (&*c1, &*c2) {
                        (Type::GlobalTy { .. }, Type::GlobalTy { .. }) if c1 == c2 => {}
                        _ => return Err(NC),
                    },
                    (Some(_), None) | (None, Some(_)) => return Err(NC),
                    (None, None) => {
                        self.tm_nee_c(env, an, bn)?; // inferred □(Δ ⊢ Ty l): ignored
                    }
                }
                let t = D::inst_ty_motive(self, env, arec, &am.ty_motive, acl, actx, an)?;
                Ok((t, (*al1).clone()))
            }
            (
                TmView::ElimCodeTm {
                    ty_motive_level: al1,
                    tm_motive_level: al2,
                    motives: am,
                    branches: ab,
                    code_level: acl,
                    ctx: actx,
                    ty: aty,
                    scrut: an,
                    rec: arec,
                },
                TmView::ElimCodeTm {
                    ty_motive_level: bl1,
                    tm_motive_level: bl2,
                    motives: bm,
                    branches: bb,
                    code_level: bcl,
                    ctx: bctx,
                    ty: bty,
                    scrut: bn,
                    rec: brec,
                },
            ) => {
                let env = &env.with_layer(Layer::Meta);
                self.rec_ca(
                    env,
                    &RecSide {
                        l1: al1,
                        l2: al2,
                        motives: Rc::clone(am),
                        branches: Rc::clone(ab),
                        rec: arec.clone(),
                    },
                    &RecSide {
                        l1: bl1,
                        l2: bl2,
                        motives: Rc::clone(bm),
                        branches: Rc::clone(bb),
                        rec: brec.clone(),
                    },
                )?;
                self.lev_eq(acl, bcl)?;
                self.ctx(env, Layer::Prog, actx, bctx)?;
                let e_d = env.in_ctx((*actx).clone(), Layer::Prog);
                let (x, y) = (
                    D::embed_ty(&e_d, Rc::clone(aty)),
                    D::embed_ty(&e_d, Rc::clone(bty)),
                );
                self.ty(&e_d, &x, &y, &Level::succ((*acl).clone()))?;
                match (
                    D::box_tm_payload(self, env, an)?,
                    D::box_tm_payload(self, env, bn)?,
                ) {
                    (Some(c1), Some(c2)) => match (&*c1, &*c2) {
                        (Term::GlobalTm { .. }, Term::GlobalTm { .. }) if c1 == c2 => {}
                        _ => return Err(NC),
                    },
                    (Some(_), None) | (None, Some(_)) => return Err(NC),
                    (None, None) => {
                        self.tm_nee_c(env, an, bn)?; // inferred □(Δ ⊢ T @ l): ignored
                    }
                }
                // Conclusion at l₂ (the ch. 04 typing rule; the ch. 06 rule
                // writes l₁, a typo).
                let t = D::inst_tm_motive(
                    self,
                    env,
                    arec,
                    &am.tm_motive,
                    acl,
                    actx,
                    aty,
                    an,
                )?;
                Ok((t, (*al2).clone()))
            }
            _ => Err(NC),
        }
    }

    // -- the C_A bundle for neutral recursors -------------------------------

    /// Ch. 06 `C_A`: motive levels, both motives, and all 56 branches, each
    /// branch compared at its instantiated motive type under its ch. 04
    /// telescope (`G_M G_Typ G_Trm`). Branch types and telescope entry
    /// types are built from the *left* side (left-biased, like all
    /// inference here). The telescope tables live in [`crate::rec`],
    /// shared with the type checker.
    ///
    /// The tables produce **raw syntax** scoped in Γ-plus-telescope, which is
    /// then embedded into the domain at the side's own [`Dom::RecCtx`]; only
    /// Γ's length and base reach [`rec::branch_specs`].
    fn rec_ca(
        &mut self,
        env: &Env<'v>,
        a: &RecSide<'_, 'v, D>,
        b: &RecSide<'_, 'v, D>,
    ) -> R {
        self.lev_eq(a.l1, b.l1)?;
        self.lev_eq(a.l2, b.l2)?;

        // G_M: the two motives, each under its scope.
        let motive_specs = rec::motive_specs(a.l1, a.l2);
        let ma = rec::motive_types(&a.motives);
        let mb = rec::motive_types(&b.motives);
        for (spec, (x, y)) in motive_specs.iter().zip(ma.into_iter().zip(mb)) {
            let e = D::push_spec(env, &spec.tele);
            let x = D::embed_ty_at(&a.rec, &e, Rc::clone(x));
            let y = D::embed_ty_at(&b.rec, &e, Rc::clone(y));
            self.ty(&e, &x, &y, &spec.level)?;
        }

        // G_Typ G_Trm: the 56 branches, each at its instantiated motive
        // type under its telescope.
        let branch_specs = rec::branch_specs(&a.motives, a.l1, a.l2, &env.gamma);
        let ba = rec::branch_terms(&a.branches);
        let bb = rec::branch_terms(&b.branches);
        for (spec, (x, y)) in branch_specs.iter().zip(ba.into_iter().zip(bb)) {
            let e = D::push_spec(env, &spec.tele);
            let x = D::embed_tm_at(&a.rec, &e, Rc::clone(x));
            let y = D::embed_tm_at(&b.rec, &e, Rc::clone(y));
            let ty = D::embed_ty_at(&a.rec, &e, Rc::clone(&spec.ty));
            self.tm(&e, &x, &y, &ty, &spec.level)?;
        }
        Ok(())
    }
}

impl<'v> Conv<'v, Values> {
    /// [`Conv::ty_root`] over two *descriptions*
    /// (`docs/intro-by-type-design.md` §3.3). The reflexivity shortcut and
    /// the cross-head memo are the checker's, on the descriptions
    /// themselves; what reaches here is a miss, and it evaluates both sides
    /// in this query's arena and then runs the ordinary comparison. δ is as
    /// lazy as `ty_root`'s: the evaluation stops at the value machine's own
    /// weak head normal form and `ty_w` decides when to unfold.
    fn ity_root(&mut self, env: &Env<'v>, a: &ITy, b: &ITy, l: &Level) -> R {
        self.spend()?;
        let d = env.gamma.entries.len() as u32;
        let mut wa = dom::values::eval_ity(self, env, a, d, false)?;
        let mut wb = dom::values::eval_ity(self, env, b, d, false)?;
        self.ty_w(env, &mut wa, &mut wb, l)
    }
}
