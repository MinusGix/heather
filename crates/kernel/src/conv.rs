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
//! Shape of the algorithm (ch. 06 verbatim, per DESIGN.md):
//!
//! - **Neutral comparison is inference**: `tm_ne`/`ty_ne` return the type /
//!   universe level of the left input (left-biased — sound by ch. 08); the
//!   normal-form judgments are checking and *ignore* redundant annotations
//!   that well-typedness already forces (the ch. 06 note below the
//!   application rule). The judgment-level `l` inputs are threaded for rule
//!   fidelity but never branch the algorithm — every level the rules
//!   actually check is an *annotation*, compared via [`Level::equiv`].
//! - **η-directed** comparison at all four function types (`Π`, `ΠΠ`,
//!   `(g : Ctx) ⇒`, `(U : Typ) ⇒`): compare applications to a fresh
//!   variable in the suitably extended context.
//! - **Boxed types/terms compare syntactically** (`==`; α-equality is free
//!   under de Bruijn). Code is static data — β-convertible code is *not*
//!   convertible.
//! - Neutral recursors compare motives, all 45 branches (each at its
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
//! reach their inputs through the [`dom::Dom`] accessor boundary and are
//! instantiated here at [`dom::Syn`], the rewriter. Nothing above depends on
//! that choice — the rules, the fuel accounting, the left-biased inference
//! and the layer discipline are the same for a value domain
//! (docs/nbe-conversion-design.md §13, stages 2a/2b).

use std::marker::PhantomData;
use std::rc::Rc;

use crate::layer::Layer;
use crate::level::Level;
use crate::rec::{self, gtm, gty, shift_univ_psi};
use crate::reduce::Defs;
use crate::term::{
    Branches, CtxBase, CtxEntry, GlobalBinding, GlobalCtx, GlobalVar, LocalCtx, LocalVar,
    Motives, Term, Type,
};
use crate::value::{self, shift::Outer, TmClo, TyClo};

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
    Conv::<Values>::new(fuel, psi).ty_root(&Env::new(psi, gamma, layer), a, b, level)
}

/// [`conv_type`] decided by the **rewriter** instead of the value machine.
///
/// The two are the same algorithm over two notions of weak head normal form
/// (`docs/nbe-conversion-design.md` §13), and this entry point exists so a
/// test can hold them against each other: `reduce.rs` is ch. 06's relation
/// transcribed rule for rule, and it is what the machine is measured against
/// (`tests/eval_differential.rs`). Nothing in the kernel calls it.
pub fn conv_type_rewriter(
    psi: &GlobalCtx,
    gamma: &LocalCtx,
    layer: Layer,
    a: &Type,
    b: &Type,
    level: &Level,
    fuel: u64,
) -> R {
    debug_assert!(layer.computes(), "convertibility is only invoked at computing layers");
    Conv::<Syn>::new(fuel, psi).ty_root(&Env::new(psi, gamma, layer), a, b, level)
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
    Conv::<Values>::new(fuel, psi).tm_root(&Env::new(psi, gamma, layer), a, b, ty, level)
}

/// [`conv_term`] decided by the rewriter; see [`conv_type_rewriter`].
#[allow(clippy::too_many_arguments)]
pub fn conv_term_rewriter(
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
    Conv::<Syn>::new(fuel, psi).tm_root(&Env::new(psi, gamma, layer), a, b, ty, level)
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
    let env = Env::new(psi, &LocalCtx { base: CtxBase::Nil, entries: vec![] }, layer);
    Conv::<Values>::new(fuel, psi).ctx(&env, layer, a, b)
}

/// [`conv_local_ctx`] decided by the rewriter; see [`conv_type_rewriter`].
pub fn conv_local_ctx_rewriter(
    psi: &GlobalCtx,
    layer: Layer,
    a: &LocalCtx,
    b: &LocalCtx,
    fuel: u64,
) -> R {
    debug_assert!(layer.computes(), "convertibility is only invoked at computing layers");
    let env = Env::new(psi, &LocalCtx { base: CtxBase::Nil, entries: vec![] }, layer);
    Conv::<Syn>::new(fuel, psi).ctx(&env, layer, a, b)
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
/// object for [`Dom::var_type`] — is [`Env::rho`] and [`Env::vtys`], which
/// the syntax domain never reads.
#[derive(Clone)]
struct Env {
    psi: GlobalCtx,
    gamma: LocalCtx,
    layer: Layer,
    /// The local environment of the value domain: entry `j` from the outer
    /// end is the neutral variable at level `j`, so pushing a binder assigns
    /// the level `gamma.entries.len()` and never renumbers anything.
    rho: value::Env,
    /// Γ's entry types as domain objects, innermost first — the one thing
    /// [`Dom::var_type`] needs and the filler `gamma` cannot supply.
    vtys: TyEnv,
    /// The telescope [`Dom::push_spec`] pushed to build this scope, as
    /// `(univs, globals, locals)`. Read by [`Dom::embed_ty_at`], which has to
    /// carry a recursor's stored environment across exactly that telescope.
    tele: (u32, u32, u32),
}

/// A persistent list of value-domain entry types: `Env` is cloned once per
/// binder push on conversion's hottest path, so this must not be a `Vec`.
#[derive(Clone)]
struct TyEnv(Option<Rc<TyEnvNode>>);

struct TyEnvNode {
    ty: Rc<TyClo>,
    level: Level,
    rest: TyEnv,
}

impl TyEnv {
    fn empty() -> TyEnv {
        TyEnv(None)
    }

    fn push(&self, ty: Rc<TyClo>, level: Level) -> TyEnv {
        TyEnv(Some(Rc::new(TyEnvNode { ty, level, rest: self.clone() })))
    }

    /// The entry `i` binders out from the innermost one.
    fn nth(&self, i: u32) -> Option<(&Rc<TyClo>, &Level)> {
        let mut cur = self;
        let mut k = i;
        loop {
            let n = cur.0.as_ref()?;
            if k == 0 {
                return Some((&n.ty, &n.level));
            }
            k -= 1;
            cur = &n.rest;
        }
    }

    /// Outermost first.
    fn to_vec(&self) -> Vec<(Rc<TyClo>, Level)> {
        let mut out = Vec::new();
        let mut cur = self;
        while let Some(n) = cur.0.as_ref() {
            out.push((Rc::clone(&n.ty), n.level.clone()));
            cur = &n.rest;
        }
        out.reverse();
        out
    }
}

/// The value-domain reading of a syntactic Γ: the identity environment of
/// its variables, and each entry's type as a closure over the *prefix* it is
/// scoped in.
fn value_scope(gamma: &LocalCtx) -> (value::Env, TyEnv) {
    let mut rho = value::Env::empty();
    let mut vtys = TyEnv::empty();
    for (i, e) in gamma.entries.iter().enumerate() {
        vtys = vtys.push(Rc::new(TyClo::new(rho.clone(), Rc::clone(&e.ty))), e.level.clone());
        rho = rho.push(Rc::new(TmClo::val(Rc::new(value::Val::var(i as u32)))));
    }
    (rho, vtys)
}

impl Env {
    fn new(psi: &GlobalCtx, gamma: &LocalCtx, layer: Layer) -> Env {
        let (rho, vtys) = value_scope(gamma);
        Env {
            psi: psi.clone(),
            gamma: gamma.clone(),
            layer,
            rho,
            vtys,
            tele: (0, 0, 0),
        }
    }

    fn with_layer(&self, layer: Layer) -> Env {
        Env { layer, ..self.clone() }
    }

    /// Replace Γ (and the layer) — used where a rule compares inside a
    /// *different* local context, e.g. `Ψ; Δ ⊢_p T ≈ T'`. The value domain's
    /// scope is rebuilt from scratch: a different Γ is a different set of
    /// variables, at levels of its own.
    fn in_ctx(&self, gamma: LocalCtx, layer: Layer) -> Env {
        let (rho, vtys) = value_scope(&gamma);
        Env { gamma, layer, rho, vtys, tele: (0, 0, 0), ..self.clone() }
    }

    /// `Γ, x : T @ l`. Reached through [`Dom::push_entry`], never directly:
    /// at the value domain pushing a binder also extends ρ with the binder's
    /// fresh neutral, and records the entry's type as a domain object.
    ///
    /// The syntactic entry is a **filler** unless the caller has real syntax
    /// (only [`Env::in_ctx`] and [`Env::new`] do): nothing reads it but the
    /// length and the base.
    fn push_entry_syn(&self, ty: Rc<Type>, level: Level) -> Env {
        let vty = Rc::new(TyClo::new(self.rho.clone(), Rc::clone(&ty)));
        self.push_entry(ty, vty, level)
    }

    fn push_entry(&self, ty: Rc<Type>, vty: Rc<TyClo>, level: Level) -> Env {
        let mut e = self.clone();
        e.rho = e.rho.push(Rc::new(TmClo::val(Rc::new(value::Val::var(
            self.gamma.entries.len() as u32,
        )))));
        e.vtys = e.vtys.push(vty, level.clone());
        e.gamma.entries.push(CtxEntry { ty, level });
        e
    }

    /// Push a telescope: `tu` universe binders then the given global
    /// bindings (each already scoped over `L, ℓ⃗` and its Ψ-prefix). The
    /// ambient Ψ and Γ are weakened accordingly — and so, at the value
    /// domain, is every value the scope carries (`value::shift`).
    fn push_tele(&self, tu: u32, globals: Vec<GlobalBinding>) -> Env {
        let tg = globals.len() as u32;
        let mut psi = shift_univ_psi(&self.psi, tu);
        psi.extend(globals);
        let o = Outer { univs: tu, globals: tg };
        let mut vtys = TyEnv::empty();
        for (t, l) in self.vtys.to_vec() {
            vtys = vtys.push(value::shift::ty_clo(&t, o), l);
        }
        Env {
            psi,
            gamma: self.gamma.shift_univ(tu).shift_global(tg),
            layer: self.layer,
            rho: value::shift::env(&self.rho, o),
            vtys,
            tele: (tu, tg, 0),
        }
    }

    fn push_univs(&self, n: u32) -> Env {
        self.push_tele(n, vec![])
    }

    fn push_global(&self, b: GlobalBinding) -> Env {
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
        Term::Fst { pair, .. } | Term::Snd { pair, .. } => delta_head(pair, defs),
        Term::App { fun, .. }
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
struct RecSide<'a, D: Dom> {
    l1: &'a Level,
    l2: &'a Level,
    motives: Rc<Motives>,
    branches: Rc<Branches>,
    rec: D::RecCtx,
}

struct Conv<D: Dom> {
    fuel: u64,
    /// Does Ψ contain any definition at all? Decided once, because when it
    /// does not — every program before this feature, and every fixture that
    /// only declares — the δ-lazy stage below has nothing to find, and
    /// paying for it cost 1.35–1.43× on the conversion benchmarks. Telescope
    /// pushes never introduce definitions, so the answer cannot change while
    /// a comparison runs.
    has_defs: bool,
    _dom: PhantomData<D>,
}

impl<D: Dom> Conv<D> {
    fn new(fuel: u64, psi: &GlobalCtx) -> Conv<D> {
        let has_defs = psi
            .bindings
            .iter()
            .any(|b| matches!(b, GlobalBinding::Tm { body: Some(_), .. }));
        Conv { fuel, has_defs, _dom: PhantomData }
    }

    fn spend(&mut self) -> R {
        if self.fuel == 0 {
            return Err(ConvError::OutOfFuel);
        }
        self.fuel -= 1;
        Ok(())
    }

    /// The δ-environment of a comparison: definitions unfold exactly at the
    /// computing layers (see [`Defs`]). Conversion is only ever invoked at
    /// p/m, so this is transparent in practice — the gate is here so that
    /// the one invariant that must never bend is stated where it is used,
    /// not assumed from the call sites.
    fn defs<'a>(&self, env: &'a Env) -> Defs<'a> {
        if self.has_defs && env.layer.computes() {
            Defs::transparent(&env.psi)
        } else {
            Defs::opaque()
        }
    }

    /// The δ-lazy attempt: with both sides stuck at the *same* defined
    /// global head, try the ordinary comparison first — `f a⃗ ≈ f a⃗`
    /// settles on the spine, and `f`'s body is never materialized. Failure
    /// means "unfold and retry", not "not convertible".
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
    fn strip(&mut self, mut cur: D::Tm, env: &Env) -> R<D::Tm> {
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
            let strip = D::eq_fast(&lhs, &rhs)
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
    fn ty(&mut self, env: &Env, a: &D::TyC, b: &D::TyC, l: &Level) -> R {
        self.spend()?;
        let mut wa = D::whnf_ty_opaque(self, env, a)?;
        let mut wb = D::whnf_ty_opaque(self, env, b)?;
        self.ty_w(env, &mut wa, &mut wb, l)
    }

    /// [`Conv::ty`] at the **root** of a conversion, where the two sides are
    /// raw syntax the caller lends us rather than sub-structures of a form
    /// already in the domain (see [`Dom::whnf_ty_root`]).
    fn ty_root(&mut self, env: &Env, a: &Type, b: &Type, l: &Level) -> R {
        self.spend()?;
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
    fn ty_w(&mut self, env: &Env, wa: &mut D::Ty, wb: &mut D::Ty, l: &Level) -> R {
        if self.has_defs {
            if let (Some(u1), Some(u2)) =
                (D::delta_head_ty(self, env, wa), D::delta_head_ty(self, env, wb))
                && u1 == u2
                && self.delta_lazy(|c| c.ty_nf(env, wa, wb, l))?.is_some()
            {
                return Ok(());
            }
            *wa = D::delta_ty(self, env, wa)?;
            *wb = D::delta_ty(self, env, wb)?;
        }
        self.ty_nf(env, wa, wb, l)
    }

    /// `Γ ⊢ W ≈ W' : l` for weak head normal types.
    fn ty_nf(&mut self, env: &Env, a: &D::Ty, b: &D::Ty, _l: &Level) -> R {
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
            // length (docs/wf-former-design.md §5).
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
    fn ty_ne(&mut self, env: &Env, a: &D::Ty, b: &D::Ty) -> R<Level> {
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
                let ctx = ctx.shift_global(u1.0 + 1);
                self.subst(env, d1, d2, &ctx)?;
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
    fn ctx(&mut self, env: &Env, layer: Layer, a: &LocalCtx, b: &LocalCtx) -> R {
        self.spend()?;
        if a.base != b.base || a.entries.len() != b.entries.len() {
            return Err(NC);
        }
        for (k, (ea, eb)) in a.entries.iter().zip(&b.entries).enumerate() {
            let prefix = LocalCtx { base: a.base, entries: a.entries[..k].to_vec() };
            let e = env.in_ctx(prefix, layer);
            let (x, y) = (
                D::embed_ty(&e, Rc::clone(&ea.ty)),
                D::embed_ty(&e, Rc::clone(&eb.ty)),
            );
            self.ty(&e, &x, &y, &ea.level)?;
            self.lev_eq(&ea.level, &eb.level)?;
        }
        Ok(())
    }

    /// `Γ ⊢ δ ≈ δ' : Δ`, pairwise on the step terms over identical tails.
    fn subst(&mut self, env: &Env, d1: &D::Subst, d2: &D::Subst, target: &LocalCtx) -> R {
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
    fn tm(&mut self, env: &Env, a: &D::TmC, b: &D::TmC, ty: &D::TyC, l: &Level) -> R {
        self.spend()?;
        let w = D::whnf_ty(self, env, ty)?;
        let wa = D::whnf_tm_opaque(self, env, a)?;
        let wb = D::whnf_tm_opaque(self, env, b)?;
        self.tm_w(env, wa, wb, &w, l)
    }

    /// [`Conv::tm`] at the **root**; see [`Conv::ty_root`].
    fn tm_root(&mut self, env: &Env, a: &Term, b: &Term, ty: &Type, l: &Level) -> R {
        self.spend()?;
        let w = D::whnf_ty_root(self, env, ty)?;
        let wa = D::whnf_tm_root(self, env, a)?;
        let wb = D::whnf_tm_root(self, env, b)?;
        self.tm_w(env, wa, wb, &w, l)
    }

    /// The δ stage, the transp strip and the comparison, shared by the two
    /// entries above.
    #[inline]
    fn tm_w(&mut self, env: &Env, mut wa: D::Tm, mut wb: D::Tm, w: &D::Ty, l: &Level) -> R {
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
            if let (Some(u1), Some(u2)) =
                (D::delta_head(self, env, &wa), D::delta_head(self, env, &wb))
                && u1 == u2
                && self.delta_lazy(|c| c.tm_nf(env, &wa, &wb, w, l))?.is_some()
            {
                return Ok(());
            }
            wa = D::delta_tm(self, env, &wa)?;
            wb = D::delta_tm(self, env, &wb)?;
        }
        if D::is_transp(&wa) {
            wa = self.strip(wa, env)?;
        }
        if D::is_transp(&wb) {
            wb = self.strip(wb, env)?;
        }
        self.tm_nf(env, &wa, &wb, w, l)
    }

    /// `Γ ⊢ k ≈ k' : Nat @ 0` — the length/arity comparison the `Vec`, `Fin`
    /// and `Wf` families all make.
    fn tm_at_nat(&mut self, env: &Env, a: &D::TmC, b: &D::TmC) -> R {
        self.tm(env, a, b, &D::nat(), &Level::Zero)
    }

    /// `Γ ⊢ s ≈ s' : Ty l @ l+1` — two type *encodings*.
    fn tm_at_univ(&mut self, env: &Env, a: &D::TmC, b: &D::TmC, l: &Level) -> R {
        let univ = D::univ(env, l);
        self.tm(env, a, b, &univ, &Level::succ(l.clone()))
    }

    /// `Γ, x : El^l s` — the binder every dependent encoding pushes.
    fn push_el(&mut self, env: &Env, l: &Level, s: &D::TmC) -> R<Env> {
        let el = D::el(self, env, l, s)?;
        Ok(D::push_entry(env, &el, l))
    }

    /// `Γ ⊢ w ≈ w' : W @ l` for weak head normal terms at a WHNF type,
    /// directed by the type.
    fn tm_nf(&mut self, env: &Env, a: &D::Tm, b: &D::Tm, w: &D::Ty, _l: &Level) -> R {
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
            TyView::Nat => match (&D::view_tm(self, env, a), &D::view_tm(self, env, b)) {
                (TmView::Zero, TmView::Zero) => Ok(()),
                (TmView::Succ(x), TmView::Succ(y)) => self.tm_at_nat(env, x, y),
                (x, y) if x.is_nat_data() || y.is_nat_data() => Err(NC),
                _ => self.tm_nee(env, a, b).map(drop),
            },
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
                        let cod = D::weaken_ty(&w_c, 1);
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
    fn tm_nee(&mut self, env: &Env, a: &D::Tm, b: &D::Tm) -> R<(D::Ty, Level)> {
        let (t, l) = self.tm_ne(env, a, b)?;
        let w = D::whnf_ty(self, env, &t)?;
        Ok((w, l))
    }

    /// [`Conv::tm_nee`] on two *sub-structures* — an eliminator's scrutinee,
    /// an application's function. They are already in weak head normal form
    /// (the form carrying them is), so reaching their heads is a no-op at the
    /// syntax domain and a `force` at the value domain.
    fn tm_nee_c(&mut self, env: &Env, a: &D::TmC, b: &D::TmC) -> R<(D::Ty, Level)> {
        let x = D::head_tm(self, env, a)?;
        let y = D::head_tm(self, env, b)?;
        self.tm_nee(env, &x, &y)
    }

    /// `Γ ⊢ ν ≈ ν' : T @ l` for neutral terms; the type and level are
    /// *inferred* (left-biased) and returned. Layer-m elimination forms
    /// bump the ambient layer to m — their rules are stated there, and the
    /// layer index restricts only types.
    fn tm_ne(&mut self, env: &Env, a: &D::Tm, b: &D::Tm) -> R<(D::TyC, Level)> {
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
                let ctx = ctx.shift_global(u1.0 + 1);
                let ty = Rc::new(ty.shift_global(u1.0 + 1));
                self.subst(env, d1, d2, &ctx)?;
                let n = D::subst_len(d1);
                Ok((D::apply_subst_ty(self, env, d1, n, &ty)?, level))
            }
            (
                TmView::ElimNat { level: v1, motive: m1, base: z1, step: s1, scrut: n1 },
                TmView::ElimNat { level: v2, motive: m2, base: z2, step: s2, scrut: n2 },
            ) => {
                self.lev_eq(v1, v2)?;
                let e_x = D::push_entry(env, &D::nat(), &Level::Zero);
                self.ty(&e_x, m1, m2, v1)?;
                let base_ty = D::inst_ty(self, env, env, m1, &[D::zero()])?;
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
                let s1_up = D::weaken_ty(s1, 1);
                let t1_up = D::weaken_ty(t1, 1);
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
                    D::pi(self, &e_a, cl1, &lmax, &t_at_a, &D::weaken_ty(&w_ty, 2))?;
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
                    &D::weaken_ty(&w_ty, 4),
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
                    D::inst_ty(self, env, &e_step, m1, &[D::weaken_tm(&sup_af, 1)])?;
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
                    &D::weaken_ty(s1, 1),
                    &D::weaken_tm(a1, 1),
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
                TmView::App {
                    dom_level: dl1,
                    cod_level: cl1,
                    dom: s1,
                    cod: t1,
                    fun: f1,
                    arg: a1,
                },
                TmView::App {
                    dom_level: dl2,
                    cod_level: cl2,
                    dom: s2,
                    cod: t2,
                    fun: f2,
                    arg: a2,
                },
            ) => {
                self.lev_eq(dl1, dl2)?;
                self.lev_eq(cl1, cl2)?;
                self.ty(env, s1, s2, dl1)?;
                let e_x = D::push_entry(env, s1, dl1);
                self.ty(&e_x, t1, t2, cl1)?;
                // The type inferred for the heads is ignored (ch. 06: the
                // annotations of well-typed applications are already forced).
                self.tm_nee_c(env, f1, f2)?;
                self.tm(env, a1, a2, s1, dl1)?;
                Ok((D::inst_ty(self, env, env, t1, std::slice::from_ref(a1))?, (*cl1).clone()))
            }
            // fst/snd neutral congruence (extension; mirrors App — the Σ
            // annotations forced by well-typedness are compared, the pair via
            // tm_nee). These arms fire only when the projected pair is itself
            // neutral (η already handled non-neutral pairs in tm_nf).
            (
                TmView::Fst {
                    fst_level: dl1,
                    snd_level: cl1,
                    fst_ty: s1,
                    snd_ty: t1,
                    pair: p1,
                },
                TmView::Fst {
                    fst_level: dl2,
                    snd_level: cl2,
                    fst_ty: s2,
                    snd_ty: t2,
                    pair: p2,
                },
            ) => {
                self.lev_eq(dl1, dl2)?;
                self.lev_eq(cl1, cl2)?;
                self.ty(env, s1, s2, dl1)?;
                let e_x = D::push_entry(env, s1, dl1);
                self.ty(&e_x, t1, t2, cl1)?;
                self.tm_nee_c(env, p1, p2)?; // inferred Σ: redundant, ignored
                Ok((s1.clone(), (*dl1).clone()))
            }
            (
                TmView::Snd {
                    fst_level: dl1,
                    snd_level: cl1,
                    fst_ty: s1,
                    snd_ty: t1,
                    pair: p1,
                },
                TmView::Snd {
                    fst_level: dl2,
                    snd_level: cl2,
                    fst_ty: s2,
                    snd_ty: t2,
                    pair: p2,
                },
            ) => {
                self.lev_eq(dl1, dl2)?;
                self.lev_eq(cl1, cl2)?;
                self.ty(env, s1, s2, dl1)?;
                let e_x = D::push_entry(env, s1, dl1);
                self.ty(&e_x, t1, t2, cl1)?;
                self.tm_nee_c(env, p1, p2)?;
                let fst_p = D::proj(self, env, true, dl1, cl1, s1, t1, p1)?;
                Ok((D::inst_ty(self, env, env, t1, std::slice::from_ref(&fst_p))?, (*cl1).clone()))
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

    /// Ch. 06 `C_A`: motive levels, both motives, and all 45 branches, each
    /// branch compared at its instantiated motive type under its ch. 04
    /// telescope (`G_M G_Typ G_Trm`). Branch types and telescope entry
    /// types are built from the *left* side (left-biased, like all
    /// inference here). The telescope tables live in [`crate::rec`],
    /// shared with the type checker.
    ///
    /// The tables produce **raw syntax** scoped in Γ-plus-telescope, which is
    /// then embedded into the domain at the side's own [`Dom::RecCtx`]; only
    /// Γ's length and base reach [`rec::branch_specs`].
    fn rec_ca(&mut self, env: &Env, a: &RecSide<D>, b: &RecSide<D>) -> R {
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

        // G_Typ G_Trm: the 45 branches, each at its instantiated motive
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
