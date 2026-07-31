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

use std::rc::Rc;

use crate::layer::Layer;
use crate::level::Level;
use crate::rec::{
    self, g_ctx, gtm, gty, inst_tm_motive, inst_ty_motive, lvar, shift_univ_psi,
};
use crate::reduce::{step_term, step_term_delta, step_type, step_type_delta, Defs};
use crate::subst::{GlobalEntry, GlobalSubst};
use crate::term::{
    wf_step_telescope, Branches, CtxBase, CtxEntry, GlobalBinding, GlobalCtx, GlobalVar,
    LocalCtx, LocalSubst, LocalVar, Motives, Term, Type,
};

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
    Conv::new(fuel, psi).ty(&Env::new(psi, gamma, layer), a, b, level)
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
    Conv::new(fuel, psi).tm(&Env::new(psi, gamma, layer), a, b, ty, level)
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
    Conv::new(fuel, psi).ctx(&env, layer, a, b)
}

// ---------------------------------------------------------------------------
// Environment
// ---------------------------------------------------------------------------

/// The ambient scope of a comparison: Ψ, Γ, and the layer index. The
/// universe context L participates only by shifting (its length is never
/// consulted), so it is not tracked. Extending any namespace clones — the
/// judgments extend scopes freely and correctness beats performance here.
#[derive(Clone)]
struct Env {
    psi: GlobalCtx,
    gamma: LocalCtx,
    layer: Layer,
}

impl Env {
    fn new(psi: &GlobalCtx, gamma: &LocalCtx, layer: Layer) -> Env {
        Env { psi: psi.clone(), gamma: gamma.clone(), layer }
    }

    fn with_layer(&self, layer: Layer) -> Env {
        Env { layer, ..self.clone() }
    }

    /// Replace Γ (and the layer) — used where a rule compares inside a
    /// *different* local context, e.g. `Ψ; Δ ⊢_p T ≈ T'`.
    fn in_ctx(&self, gamma: LocalCtx, layer: Layer) -> Env {
        Env { gamma, layer, ..self.clone() }
    }

    /// `Γ, x : T @ l`.
    fn push_entry(&self, ty: Rc<Type>, level: Level) -> Env {
        let mut e = self.clone();
        e.gamma.entries.push(CtxEntry { ty, level });
        e
    }

    /// Push a telescope: `tu` universe binders then the given global
    /// bindings (each already scoped over `L, ℓ⃗` and its Ψ-prefix). The
    /// ambient Ψ and Γ are weakened accordingly.
    fn push_tele(&self, tu: u32, globals: Vec<GlobalBinding>) -> Env {
        let tg = globals.len() as u32;
        let mut psi = shift_univ_psi(&self.psi, tu);
        psi.extend(globals);
        Env {
            psi,
            gamma: self.gamma.shift_univ(tu).shift_global(tg),
            layer: self.layer,
        }
    }

    fn push_univs(&self, n: u32) -> Env {
        self.push_tele(n, vec![])
    }

    fn push_global(&self, b: GlobalBinding) -> Env {
        self.push_tele(0, vec![b])
    }

    /// Push a full recursor telescope (universes, globals, then the
    /// recursive-call local entries).
    fn push_spec(&self, tele: &rec::Tele) -> Env {
        let mut e = self.push_tele(tele.univs, tele.globals.clone());
        for (ty, level) in &tele.locals {
            e = e.push_entry(Rc::clone(ty), level.clone());
        }
        e
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
struct RecSide<'a> {
    l1: &'a Level,
    l2: &'a Level,
    motives: &'a Motives,
    branches: &'a Branches,
}

struct Conv {
    fuel: u64,
    /// Does Ψ contain any definition at all? Decided once, because when it
    /// does not — every program before this feature, and every fixture that
    /// only declares — the δ-lazy stage below has nothing to find, and
    /// paying for it cost 1.35–1.43× on the conversion benchmarks. Telescope
    /// pushes never introduce definitions, so the answer cannot change while
    /// a comparison runs.
    has_defs: bool,
}

impl Conv {
    fn new(fuel: u64, psi: &GlobalCtx) -> Conv {
        let has_defs = psi
            .bindings
            .iter()
            .any(|b| matches!(b, GlobalBinding::Tm { body: Some(_), .. }));
        Conv { fuel, has_defs }
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

    /// `T ⇝* W`, spending one fuel per step (shared budget, unlike
    /// [`crate::reduce::whnf_type`]'s local one).
    fn whnf_ty(&mut self, t: &Type, env: &Env) -> R<Type> {
        let defs = self.defs(env);
        let mut cur = t.clone();
        while let Some(next) = step_type_delta(&cur, &env.gamma, defs) {
            self.spend()?;
            cur = next;
        }
        Ok(cur)
    }

    fn whnf_tm(&mut self, t: &Term, env: &Env) -> R<Term> {
        let defs = self.defs(env);
        let mut cur = t.clone();
        while let Some(next) = step_term_delta(&cur, &env.gamma, defs) {
            self.spend()?;
            cur = next;
        }
        Ok(cur)
    }

    /// `T ⇝* W` **without** δ: stops at a definition's spine instead of
    /// unfolding it. The first stage of the δ-lazy order described on
    /// [`Conv::ty`]; resuming with [`Conv::whnf_ty`] from here loses
    /// nothing, since weak-head reduction is deterministic and the Ψ-free
    /// relation is a sub-relation of the δ one.
    fn whnf_ty_opaque(&mut self, t: &Type, env: &Env) -> R<Type> {
        let mut cur = t.clone();
        while let Some(next) = step_type(&cur, &env.gamma) {
            self.spend()?;
            cur = next;
        }
        Ok(cur)
    }

    fn whnf_tm_opaque(&mut self, t: &Term, env: &Env) -> R<Term> {
        let mut cur = t.clone();
        while let Some(next) = step_term(&cur, &env.gamma) {
            self.spend()?;
            cur = next;
        }
        Ok(cur)
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
    fn strip(&mut self, mut cur: Term, env: &Env) -> R<Term> {
        loop {
            let Term::Transp { ty_level, ty, lhs, rhs, tm, .. } = &cur else {
                return Ok(cur);
            };
            // Fast path: syntactic endpoint equality (α-equality is free
            // under de Bruijn); the full guarded query — at the transp's
            // own annotations — only when that misses.
            let strip = lhs == rhs
                || match self.tm(env, lhs, rhs, ty, ty_level) {
                    Ok(()) => true,
                    Err(ConvError::NotConvertible) => false,
                    Err(e) => return Err(e),
                };
            if !strip {
                return Ok(cur);
            }
            self.spend()?;
            let payload = Rc::clone(tm);
            cur = self.whnf_tm(&payload, env)?;
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
    fn ty(&mut self, env: &Env, a: &Type, b: &Type, l: &Level) -> R {
        self.spend()?;
        let mut wa = self.whnf_ty_opaque(a, env)?;
        let mut wb = self.whnf_ty_opaque(b, env)?;
        if self.has_defs {
            let defs = self.defs(env);
            if let (Some(u1), Some(u2)) = (delta_head_ty(&wa, defs), delta_head_ty(&wb, defs))
                && u1 == u2
                && self.delta_lazy(|c| c.ty_nf(env, &wa, &wb, l))?.is_some()
            {
                return Ok(());
            }
            wa = self.whnf_ty(&wa, env)?;
            wb = self.whnf_ty(&wb, env)?;
        }
        self.ty_nf(env, &wa, &wb, l)
    }

    /// `Γ ⊢ W ≈ W' : l` for weak head normal types.
    fn ty_nf(&mut self, env: &Env, a: &Type, b: &Type, _l: &Level) -> R {
        match (a, b) {
            (Type::Nat, Type::Nat) => Ok(()),
            (Type::Ty(x), Type::Ty(y)) => self.lev_eq(x, y),
            (
                Type::Pi { dom_level: dl1, cod_level: cl1, dom: s1, cod: t1 },
                Type::Pi { dom_level: dl2, cod_level: cl2, dom: s2, cod: t2 },
            ) => {
                self.lev_eq(dl1, dl2)?;
                self.lev_eq(cl1, cl2)?;
                self.ty(env, s1, s2, dl1)?;
                let e = env.push_entry(Rc::clone(s1), dl1.clone());
                self.ty(&e, t1, t2, cl1)
            }
            // Id congruence (extension beyond ch. 04; kernel-v1-extensions).
            (
                Type::Id { level: l1, ty: s1, lhs: t1, rhs: u1 },
                Type::Id { level: l2, ty: s2, lhs: t2, rhs: u2 },
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
                Type::SEq { level: l1, ty: s1, lhs: t1, rhs: u1 },
                Type::SEq { level: l2, ty: s2, lhs: t2, rhs: u2 },
            ) => {
                self.lev_eq(l1, l2)?;
                self.ty(env, s1, s2, l1)?;
                self.tm(env, t1, t2, s1, l1)?;
                self.tm(env, u1, u2, s1, l1)
            }
            // Σ congruence (extension; mirrors Π).
            (
                Type::Sigma { fst_level: dl1, snd_level: cl1, fst: s1, snd: t1 },
                Type::Sigma { fst_level: dl2, snd_level: cl2, fst: s2, snd: t2 },
            ) => {
                self.lev_eq(dl1, dl2)?;
                self.lev_eq(cl1, cl2)?;
                self.ty(env, s1, s2, dl1)?;
                let e = env.push_entry(Rc::clone(s1), dl1.clone());
                self.ty(&e, t1, t2, cl1)
            }
            // Unit/Empty congruence (extension; nullary formers).
            // Unit^l / Empty^l congruence (extension): level-indexed, so the
            // levels must agree — up to `≈`, not `==`.
            (Type::Unit { level: l1 }, Type::Unit { level: l2 })
            | (Type::Empty { level: l1 }, Type::Empty { level: l2 })
            | (Type::SEmpty { level: l1 }, Type::SEmpty { level: l2 }) => self.lev_eq(l1, l2),
            // Sum congruence (extension; non-dependent, so no binder push).
            (
                Type::Sum { lhs_level: dl1, rhs_level: cl1, lhs: s1, rhs: t1 },
                Type::Sum { lhs_level: dl2, rhs_level: cl2, lhs: s2, rhs: t2 },
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
                Type::Vec { level: l1, elem: e1, len: k1 },
                Type::Vec { level: l2, elem: e2, len: k2 },
            ) => {
                self.lev_eq(l1, l2)?;
                self.ty(env, e1, e2, l1)?;
                self.tm(env, k1, k2, &Type::Nat, &Level::Zero)
            }
            (Type::Fin { len: k1 }, Type::Fin { len: k2 }) => {
                self.tm(env, k1, k2, &Type::Nat, &Level::Zero)
            }
            // Wf congruence (extension): the arity is a Nat term under the
            // shape binder, so it is compared as a term in (Γ, x : S).
            (
                Type::Wf { level: l1, shape: s1, arity: n1 },
                Type::Wf { level: l2, shape: s2, arity: n2 },
            ) => {
                self.lev_eq(l1, l2)?;
                self.ty(env, s1, s2, l1)?;
                let e_x = env.push_entry(Rc::clone(s1), l1.clone());
                self.tm(&e_x, n1, n2, &Type::Nat, &Level::Zero)
            }
            // W congruence (extension; mirrors Π/Σ).
            (
                Type::W { shape_level: dl1, pos_level: cl1, shape: s1, pos: t1 },
                Type::W { shape_level: dl2, pos_level: cl2, shape: s2, pos: t2 },
            ) => {
                self.lev_eq(dl1, dl2)?;
                self.lev_eq(cl1, cl2)?;
                self.ty(env, s1, s2, dl1)?;
                let e = env.push_entry(Rc::clone(s1), dl1.clone());
                self.ty(&e, t1, t2, cl1)
            }
            // -- layer-m type formers: mismatch outside layer m -------------
            (
                Type::UPi { num_vars: n1, level: v1, body: b1 },
                Type::UPi { num_vars: n2, level: v2, body: b2 },
            ) => {
                if env.layer != Layer::Meta || n1 != n2 {
                    return Err(NC);
                }
                self.lev_eq(v1, v2)?;
                let e = env.push_univs(*n1);
                self.ty(&e, b1, b2, v1)
            }
            (
                Type::CtxPi { level: v1, body: b1 },
                Type::CtxPi { level: v2, body: b2 },
            ) => {
                if env.layer != Layer::Meta {
                    return Err(NC);
                }
                self.lev_eq(v1, v2)?;
                let e = env.push_global(GlobalBinding::Ctx);
                self.ty(&e, b1, b2, v1)
            }
            (
                Type::TyPi { ctx: c1, arg_level: a1, body_level: bl1, body: b1 },
                Type::TyPi { ctx: c2, arg_level: a2, body_level: bl2, body: b2 },
            ) => {
                if env.layer != Layer::Meta {
                    return Err(NC);
                }
                self.lev_eq(a1, a2)?;
                self.lev_eq(bl1, bl2)?;
                self.ctx(env, Layer::Prog, c1, c2)?;
                let e = env.push_global(GlobalBinding::Ty {
                    ctx: c1.clone(),
                    layer: Layer::Prog,
                    level: a1.clone(),
                });
                self.ty(&e, b1, b2, bl1)
            }
            (
                Type::CodeTy { ctx: c1, level: v1 },
                Type::CodeTy { ctx: c2, level: v2 },
            ) => {
                if env.layer != Layer::Meta {
                    return Err(NC);
                }
                self.lev_eq(v1, v2)?;
                self.ctx(env, Layer::Prog, c1, c2)
            }
            (
                Type::CodeTm { ctx: c1, ty: t1, level: v1 },
                Type::CodeTm { ctx: c2, ty: t2, level: v2 },
            ) => {
                if env.layer != Layer::Meta {
                    return Err(NC);
                }
                self.lev_eq(v1, v2)?;
                self.ctx(env, Layer::Prog, c1, c2)?;
                let e = env.in_ctx(c1.clone(), Layer::Prog);
                self.ty(&e, t1, t2, v1)
            }
            // -- neutrals ---------------------------------------------------
            (
                Type::El { .. } | Type::GlobalTy { .. },
                Type::El { .. } | Type::GlobalTy { .. },
            ) => self.ty_ne(env, a, b).map(drop),
            _ => Err(NC),
        }
    }

    /// `Γ ⊢ V ≈ V' : l` for neutral types; the level is *inferred*
    /// (left-biased) and returned.
    fn ty_ne(&mut self, env: &Env, a: &Type, b: &Type) -> R<Level> {
        self.spend()?;
        match (a, b) {
            (
                Type::GlobalTy { var: u1, subst: d1 },
                Type::GlobalTy { var: u2, subst: d2 },
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
                Type::El { level: l1, tm: n1 },
                Type::El { level: l2, tm: n2 },
            ) => {
                self.lev_eq(l1, l2)?;
                self.tm_nee(env, n1, n2)?; // inferred `Ty l`: redundant, ignored
                Ok(l1.clone())
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
            self.ty(&e, &ea.ty, &eb.ty, &ea.level)?;
            self.lev_eq(&ea.level, &eb.level)?;
        }
        Ok(())
    }

    /// `Γ ⊢ δ ≈ δ' : Δ`, pairwise on the step terms over identical tails.
    fn subst(&mut self, env: &Env, d1: &LocalSubst, d2: &LocalSubst, target: &LocalCtx) -> R {
        self.spend()?;
        if d1.tail != d2.tail
            || d1.terms.len() != target.entries.len()
            || d2.terms.len() != target.entries.len()
        {
            return Err(NC);
        }
        for (k, e) in target.entries.iter().enumerate() {
            let prefix = LocalSubst { tail: d1.tail, terms: d1.terms[..k].to_vec() };
            let ty = e.ty.apply_local(&prefix);
            self.tm(env, &d1.terms[k], &d2.terms[k], &ty, &e.level)?;
        }
        Ok(())
    }

    // -- terms --------------------------------------------------------------

    /// `Γ ⊢ t ≈ t' : T @ l`: reduce the type and both terms to WHNF, then
    /// compare type-directed.
    fn tm(&mut self, env: &Env, a: &Term, b: &Term, ty: &Type, l: &Level) -> R {
        self.spend()?;
        let w = self.whnf_ty(ty, env)?;
        // δ-lazy stage (extension; see [`Conv::ty`]): stop at a definition's
        // spine, and when both sides stop at the *same* one, try the spine
        // comparison before unfolding anything.
        // whnf, then strip transp heads whose endpoints convert
        // ([`Conv::strip`]). The check is inline (not a whnf-wrapping
        // helper) so the hot path — no transp head, i.e. every pre-sEq
        // program — pays one discriminant read and zero extra `Term`
        // moves; the helper layering cost 1.35× on `conv/computed-numeral`
        // (`scripts/bench --check`, 2026-07-28).
        let mut wa = self.whnf_tm_opaque(a, env)?;
        let mut wb = self.whnf_tm_opaque(b, env)?;
        if self.has_defs {
            let defs = self.defs(env);
            if let (Some(u1), Some(u2)) = (delta_head(&wa, defs), delta_head(&wb, defs))
                && u1 == u2
                && self.delta_lazy(|c| c.tm_nf(env, &wa, &wb, &w, l))?.is_some()
            {
                return Ok(());
            }
            wa = self.whnf_tm(&wa, env)?;
            wb = self.whnf_tm(&wb, env)?;
        }
        if matches!(wa, Term::Transp { .. }) {
            wa = self.strip(wa, env)?;
        }
        if matches!(wb, Term::Transp { .. }) {
            wb = self.strip(wb, env)?;
        }
        self.tm_nf(env, &wa, &wb, &w, l)
    }

    /// `Γ ⊢ w ≈ w' : W @ l` for weak head normal terms at a WHNF type,
    /// directed by the type.
    fn tm_nf(&mut self, env: &Env, a: &Term, b: &Term, w: &Type, _l: &Level) -> R {
        match w {
            // η: Γ, x : S ⊢ app(w↑; l,l'; x:S↑.T↑; x) ≈ app(w'↑; …; x) : T
            Type::Pi { dom_level, cod_level, dom, cod } => {
                // The `cod` annotation moves under the App binder: the Π
                // variable maps to the App's bound variable, Γ weakens by 2.
                let cod_ann = Rc::new(cod.apply_local(
                    &LocalSubst::id(&env.gamma)
                        .shift_local(2)
                        .extended(Rc::new(Term::Var(LocalVar(0)))),
                ));
                let app = |t: &Term| Term::App {
                    fun: Rc::new(t.shift_local(1)),
                    dom_level: dom_level.clone(),
                    cod_level: cod_level.clone(),
                    dom: Rc::new(dom.shift_local(1)),
                    cod: Rc::clone(&cod_ann),
                    arg: Rc::new(Term::Var(LocalVar(0))),
                };
                let e = env.push_entry(Rc::clone(dom), dom_level.clone());
                self.tm(&e, &app(a), &app(b), cod, cod_level)
            }
            // η: L, ℓ⃗ ⊢ w↑ $ ℓ⃗ ≈ w'↑ $ ℓ⃗ : T
            Type::UPi { num_vars, level, body } => {
                if env.layer != Layer::Meta {
                    return Err(NC);
                }
                let n = *num_vars;
                let levels: Vec<Level> = (0..n).rev().map(lvar).collect();
                let uapp = |t: &Term| Term::UApp {
                    fun: Rc::new(t.shift_univ(n)),
                    levels: levels.clone(),
                };
                let e = env.push_univs(n);
                self.tm(&e, &uapp(a), &uapp(b), body, level)
            }
            // η: Ψ, g : Ctx ⊢ w↑ @ g ≈ w'↑ @ g : T
            Type::CtxPi { level, body } => {
                if env.layer != Layer::Meta {
                    return Err(NC);
                }
                let capp = |t: &Term| Term::CtxApp {
                    fun: Rc::new(t.shift_global(1)),
                    ctx: g_ctx(0),
                };
                let e = env.push_global(GlobalBinding::Ctx);
                self.tm(&e, &capp(a), &capp(b), body, level)
            }
            // η: Ψ, U : Typ_p(Δ, l) ⊢ w↑ @ U^{id_Δ} ≈ w'↑ @ U^{id_Δ} : T
            Type::TyPi { ctx, arg_level, body_level, body } => {
                if env.layer != Layer::Meta {
                    return Err(NC);
                }
                let ctx_up = ctx.shift_global(1);
                let arg = Rc::new(gty(0, &ctx_up));
                let tapp = |t: &Term| Term::TyApp {
                    fun: Rc::new(t.shift_global(1)),
                    arg: Rc::clone(&arg),
                };
                let e = env.push_global(GlobalBinding::Ty {
                    ctx: ctx.clone(),
                    layer: Layer::Prog,
                    level: arg_level.clone(),
                });
                self.tm(&e, &tapp(a), &tapp(b), body, body_level)
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
            Type::CodeTy { .. } => match (a, b) {
                (Term::BoxTy(t1), Term::BoxTy(t2)) => {
                    if code_eq(&**t1, &**t2) { Ok(()) } else { Err(NC) }
                }
                (Term::BoxTy(_), _) | (_, Term::BoxTy(_)) => Err(NC),
                _ => self.tm_nee(env, a, b).map(drop),
            },
            Type::CodeTm { .. } => match (a, b) {
                (Term::BoxTm(t1), Term::BoxTm(t2)) => {
                    if code_eq(&**t1, &**t2) { Ok(()) } else { Err(NC) }
                }
                (Term::BoxTm(_), _) | (_, Term::BoxTm(_)) => Err(NC),
                _ => self.tm_nee(env, a, b).map(drop),
            },
            Type::Nat => match (a, b) {
                (Term::Zero, Term::Zero) => Ok(()),
                (Term::Succ(x), Term::Succ(y)) => {
                    self.tm(env, x, y, &Type::Nat, &Level::Zero)
                }
                (Term::Zero | Term::Succ(_), _) | (_, Term::Zero | Term::Succ(_)) => {
                    Err(NC)
                }
                _ => self.tm_nee(env, a, b).map(drop),
            },
            Type::Ty(_) => match (a, b) {
                (Term::TmNat, Term::TmNat) => Ok(()),
                (Term::TmTy(x), Term::TmTy(y)) => self.lev_eq(x, y),
                (
                    Term::TmPi { dom_level: dl1, cod_level: cl1, dom: s1, cod: t1 },
                    Term::TmPi { dom_level: dl2, cod_level: cl2, dom: s2, cod: t2 },
                ) => {
                    self.lev_eq(dl1, dl2)?;
                    self.lev_eq(cl1, cl2)?;
                    self.tm(env, s1, s2, &Type::Ty(dl1.clone()), &Level::succ(dl1.clone()))?;
                    let el = Type::El { level: dl1.clone(), tm: Rc::clone(s1) };
                    let e = env.push_entry(Rc::new(el), dl1.clone());
                    self.tm(&e, t1, t2, &Type::Ty(cl1.clone()), &Level::succ(cl1.clone()))
                }
                // TmId congruence (extension).
                (
                    Term::TmId { level: l1, ty: s1, lhs: t1, rhs: u1 },
                    Term::TmId { level: l2, ty: s2, lhs: t2, rhs: u2 },
                ) => {
                    self.lev_eq(l1, l2)?;
                    self.tm(env, s1, s2, &Type::Ty(l1.clone()), &Level::succ(l1.clone()))?;
                    let el = Type::El { level: l1.clone(), tm: Rc::clone(s1) };
                    self.tm(env, t1, t2, &el, l1)?;
                    self.tm(env, u1, u2, &el, l1)
                }
                // TmSEq congruence (extension; mirrors TmId — the
                // *encoding* compares structurally like any code; only
                // terms AT sEq type are irrelevant).
                (
                    Term::TmSEq { level: l1, ty: s1, lhs: t1, rhs: u1 },
                    Term::TmSEq { level: l2, ty: s2, lhs: t2, rhs: u2 },
                ) => {
                    self.lev_eq(l1, l2)?;
                    self.tm(env, s1, s2, &Type::Ty(l1.clone()), &Level::succ(l1.clone()))?;
                    let el = Type::El { level: l1.clone(), tm: Rc::clone(s1) };
                    self.tm(env, t1, t2, &el, l1)?;
                    self.tm(env, u1, u2, &el, l1)
                }
                // TmSigma congruence (extension; mirrors TmPi).
                (
                    Term::TmSigma { fst_level: dl1, snd_level: cl1, fst: s1, snd: t1 },
                    Term::TmSigma { fst_level: dl2, snd_level: cl2, fst: s2, snd: t2 },
                ) => {
                    self.lev_eq(dl1, dl2)?;
                    self.lev_eq(cl1, cl2)?;
                    self.tm(env, s1, s2, &Type::Ty(dl1.clone()), &Level::succ(dl1.clone()))?;
                    let el = Type::El { level: dl1.clone(), tm: Rc::clone(s1) };
                    let e = env.push_entry(Rc::new(el), dl1.clone());
                    self.tm(&e, t1, t2, &Type::Ty(cl1.clone()), &Level::succ(cl1.clone()))
                }
                // TmUnit/TmEmpty congruence (extension; nullary encodings).
                (Term::TmUnit { level: l1 }, Term::TmUnit { level: l2 })
                | (Term::TmEmpty { level: l1 }, Term::TmEmpty { level: l2 })
                | (Term::TmSEmpty { level: l1 }, Term::TmSEmpty { level: l2 }) => {
                    self.lev_eq(l1, l2)
                }
                // TmSum congruence (extension; non-dependent, mirrors TmSigma).
                (
                    Term::TmSum { lhs_level: dl1, rhs_level: cl1, lhs: s1, rhs: t1 },
                    Term::TmSum { lhs_level: dl2, rhs_level: cl2, lhs: s2, rhs: t2 },
                ) => {
                    self.lev_eq(dl1, dl2)?;
                    self.lev_eq(cl1, cl2)?;
                    self.tm(env, s1, s2, &Type::Ty(dl1.clone()), &Level::succ(dl1.clone()))?;
                    self.tm(env, t1, t2, &Type::Ty(cl1.clone()), &Level::succ(cl1.clone()))
                }
                // TmW congruence (extension; mirrors TmPi/TmSigma).
                (
                    Term::TmW { shape_level: dl1, pos_level: cl1, shape: s1, pos: t1 },
                    Term::TmW { shape_level: dl2, pos_level: cl2, shape: s2, pos: t2 },
                ) => {
                    self.lev_eq(dl1, dl2)?;
                    self.lev_eq(cl1, cl2)?;
                    self.tm(env, s1, s2, &Type::Ty(dl1.clone()), &Level::succ(dl1.clone()))?;
                    let el = Type::El { level: dl1.clone(), tm: Rc::clone(s1) };
                    let e = env.push_entry(Rc::new(el), dl1.clone());
                    self.tm(&e, t1, t2, &Type::Ty(cl1.clone()), &Level::succ(cl1.clone()))
                }
                // TmVec/TmFin congruence (extension): the length is compared
                // at Nat in the ambient scope — no binder, unlike TmWf.
                (
                    Term::TmVec { level: l1, elem: s1, len: k1 },
                    Term::TmVec { level: l2, elem: s2, len: k2 },
                ) => {
                    self.lev_eq(l1, l2)?;
                    self.tm(env, s1, s2, &Type::Ty(l1.clone()), &Level::succ(l1.clone()))?;
                    self.tm(env, k1, k2, &Type::Nat, &Level::Zero)
                }
                (Term::TmFin { len: k1 }, Term::TmFin { len: k2 }) => {
                    self.tm(env, k1, k2, &Type::Nat, &Level::Zero)
                }
                // TmWf congruence (extension): the arity is compared at Nat
                // under the shape binder, mirroring TmW's positions.
                (
                    Term::TmWf { level: l1, shape: s1, arity: n1 },
                    Term::TmWf { level: l2, shape: s2, arity: n2 },
                ) => {
                    self.lev_eq(l1, l2)?;
                    self.tm(env, s1, s2, &Type::Ty(l1.clone()), &Level::succ(l1.clone()))?;
                    let el = Type::El { level: l1.clone(), tm: Rc::clone(s1) };
                    let e = env.push_entry(Rc::new(el), l1.clone());
                    self.tm(&e, n1, n2, &Type::Nat, &Level::Zero)
                }
                (
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
                    | Term::TmSEq { .. }
                    | Term::TmSEmpty { .. },
                    _,
                )
                | (
                    _,
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
                    | Term::TmSEq { .. }
                    | Term::TmSEmpty { .. },
                ) => Err(NC),
                _ => self.tm_nee(env, a, b).map(drop),
            },
            // Id (extension): refl congruence on the point; else neutral.
            // The refl annotations are forced by well-typedness at this Id
            // type, so only the point is compared.
            Type::Id { level, ty, .. } => match (a, b) {
                (Term::Refl { tm: x, .. }, Term::Refl { tm: y, .. }) => {
                    self.tm(env, x, y, ty, level)
                }
                (Term::Refl { .. }, _) | (_, Term::Refl { .. }) => Err(NC),
                _ => self.tm_nee(env, a, b).map(drop),
            },
            // Σ η (extension): surjective pairing — type-directed like the Π
            // η arm, so it fires on literal pairs, neutrals, or mixtures.
            // Compare `fst a ≈ fst b : S` and `snd a ≈ snd b : T[fst a/x]`.
            Type::Sigma { fst_level, snd_level, fst, snd } => {
                let proj = |head: &Term, first: bool| {
                    let f = |pair: Rc<Term>| {
                        (
                            fst_level.clone(),
                            snd_level.clone(),
                            Rc::clone(fst),
                            Rc::clone(snd),
                            pair,
                        )
                    };
                    let (fl, sl, ft, st, pair) = f(Rc::new(head.clone()));
                    if first {
                        Term::Fst { fst_level: fl, snd_level: sl, fst_ty: ft, snd_ty: st, pair }
                    } else {
                        Term::Snd { fst_level: fl, snd_level: sl, fst_ty: ft, snd_ty: st, pair }
                    }
                };
                self.tm(env, &proj(a, true), &proj(b, true), fst, fst_level)?;
                let snd_ty = snd.apply_local(
                    &LocalSubst::id(&env.gamma).extended(Rc::new(proj(a, true))),
                );
                self.tm(env, &proj(a, false), &proj(b, false), &snd_ty, snd_level)
            }
            // Unit η (extension): proof irrelevance — every term of Unit type
            // is convertible to ⟨⟩, hence to each other. Type-directed like Σ
            // η, so it fires on ⟨⟩, neutrals, or mixtures without inspecting
            // either side.
            Type::Unit { .. } => Ok(()),
            // sEq irrelevance (extension; docs/sprop-design.md §5.2): the
            // Unit pattern generalized — any two proofs of a strict equality
            // are definitionally equal. This arm is also what lets the
            // transp congruence in `tm_ne` skip the proofs, and what makes
            // UIP at sEq definitional (`p ≡ srefl`) rather than a theorem.
            // Both of Unit's ch. 07 §4 consequences apply verbatim:
            // presupposition holds by assumption on the caller, and the arm
            // must sit here in `tm_nf`, ahead of any structural fallback.
            Type::SEq { .. } => Ok(()),
            // sEmpty irrelevance (extension; docs/sprop-design.md §2.2):
            // unlike Empty (structural neutrals, above-adjacent arm), any
            // two absurdity proofs are convertible — vacuously sound, the
            // type is uninhabited in consistent contexts.
            Type::SEmpty { .. } => Ok(()),
            // Empty (extension): no canonical inhabitants, so only neutrals can
            // appear; compare them structurally.
            Type::Empty { .. } => self.tm_nee(env, a, b).map(drop),
            // Sum (extension): a positive type — the two constructors match
            // like `Zero`/`Succ` at `Nat`. The annotations on inl/inr are
            // forced by well-typedness at this sum type, so only the injected
            // value is compared; a tag mismatch is `NotConvertible`; neutrals
            // (a stuck `case`, a variable) fall through to structural
            // comparison.
            Type::Sum { lhs_level, rhs_level, lhs, rhs } => match (a, b) {
                (Term::Inl { val: x, .. }, Term::Inl { val: y, .. }) => {
                    self.tm(env, x, y, lhs, lhs_level)
                }
                (Term::Inr { val: x, .. }, Term::Inr { val: y, .. }) => {
                    self.tm(env, x, y, rhs, rhs_level)
                }
                (Term::Inl { .. } | Term::Inr { .. }, _)
                | (_, Term::Inl { .. } | Term::Inr { .. }) => Err(NC),
                _ => self.tm_nee(env, a, b).map(drop),
            },
            // W (extension): a positive type — `sup` matches like the sum
            // constructors. The annotations on sup are forced by
            // well-typedness at this W type, so only the label and the
            // subtree function are compared (the latter at the left label's
            // instantiated Π type, left-biased); neutrals (a stuck elim_W, a
            // variable) fall through to structural comparison.
            Type::W { shape_level, pos_level, shape, pos } => match (a, b) {
                (
                    Term::Sup { label: a1, children: f1, .. },
                    Term::Sup { label: a2, children: f2, .. },
                ) => {
                    self.tm(env, a1, a2, shape, shape_level)?;
                    let lmax = Level::max(shape_level.clone(), pos_level.clone());
                    let pos_at =
                        pos.apply_local(&LocalSubst::id(&env.gamma).extended(Rc::clone(a1)));
                    let f_ty = Type::Pi {
                        dom_level: pos_level.clone(),
                        cod_level: lmax.clone(),
                        dom: Rc::new(pos_at),
                        cod: Rc::new(w.shift_local(1)),
                    };
                    self.tm(env, f1, f2, &f_ty, &Level::max(pos_level.clone(), lmax))
                }
                (Term::Sup { .. }, _) | (_, Term::Sup { .. }) => Err(NC),
                _ => self.tm_nee(env, a, b).map(drop),
            },
            // Wf (extension): positive, like W — but the children compare at
            // a `Vec`, so the comparison descends through `Σ`-η and bottoms
            // out in `Unit`'s proof irrelevance. That is the whole reason
            // this former exists (docs/wf-former-design.md §5): no funext is
            // reachable from here, because there is no function to compare.
            Type::Wf { level, shape, arity } => match (a, b) {
                (
                    Term::Supf { label: a1, children: c1, .. },
                    Term::Supf { label: a2, children: c2, .. },
                ) => {
                    self.tm(env, a1, a2, shape, level)?;
                    // Children at Vec(Wf; n[a₁/x]), left-biased like W's.
                    let arity_at =
                        arity.apply_local(&LocalSubst::id(&env.gamma).extended(Rc::clone(a1)));
                    let cs_ty = Type::Vec {
                        level: level.clone(),
                        elem: Rc::new(w.clone()),
                        len: Rc::new(arity_at),
                    };
                    self.tm(env, c1, c2, &cs_ty, level)
                }
                (Term::Supf { .. }, _) | (_, Term::Supf { .. }) => Err(NC),
                _ => self.tm_nee(env, a, b).map(drop),
            },
            // Neutral type: only neutral terms inhabit it. `Vec`/`Fin` reach
            // here only at a neutral length (a canonical one reduces to
            // Σ/Unit resp. Sum/Empty first, and those arms then supply the
            // η) — so they behave exactly like the other neutral types.
            Type::El { .. }
            | Type::GlobalTy { .. }
            | Type::Vec { .. }
            | Type::Fin { .. } => self.tm_nee(env, a, b).map(drop),
        }
    }

    /// Neutral comparison with the inferred type reduced to WHNF.
    fn tm_nee(&mut self, env: &Env, a: &Term, b: &Term) -> R<(Type, Level)> {
        let (t, l) = self.tm_ne(env, a, b)?;
        let w = self.whnf_ty(&t, env)?;
        Ok((w, l))
    }

    /// `Γ ⊢ ν ≈ ν' : T @ l` for neutral terms; the type and level are
    /// *inferred* (left-biased) and returned. Layer-m elimination forms
    /// bump the ambient layer to m — their rules are stated there, and the
    /// layer index restricts only types.
    fn tm_ne(&mut self, env: &Env, a: &Term, b: &Term) -> R<(Type, Level)> {
        self.spend()?;
        match (a, b) {
            (Term::Var(x), Term::Var(y)) => {
                if x != y {
                    return Err(NC);
                }
                let Some(i) = env.gamma.entries.len().checked_sub(1 + x.0 as usize)
                else {
                    return Err(NC);
                };
                let e = &env.gamma.entries[i];
                Ok((e.ty.shift_local(x.0 + 1), e.level.clone()))
            }
            (
                Term::GlobalTm { var: u1, subst: d1 },
                Term::GlobalTm { var: u2, subst: d2 },
            ) => {
                if u1 != u2 {
                    return Err(NC);
                }
                let Some(GlobalBinding::Tm { ctx, layer, ty, level, .. }) = lookup(&env.psi, *u1)
                else {
                    return Err(NC);
                };
                // i' ∈ {v, c} is forced by the binding form; i' ≤ i:
                if *layer > env.layer {
                    return Err(NC);
                }
                let level = level.clone();
                let ctx = ctx.shift_global(u1.0 + 1);
                let ty = ty.shift_global(u1.0 + 1);
                self.subst(env, d1, d2, &ctx)?;
                Ok((ty.apply_local(d1), level))
            }
            (
                Term::ElimNat { level: v1, motive: m1, base: z1, step: s1, scrut: n1 },
                Term::ElimNat { level: v2, motive: m2, base: z2, step: s2, scrut: n2 },
            ) => {
                self.lev_eq(v1, v2)?;
                let e_x = env.push_entry(Rc::new(Type::Nat), Level::Zero);
                self.ty(&e_x, m1, m2, v1)?;
                let base_ty =
                    m1.apply_local(&LocalSubst::id(&env.gamma).extended(Rc::new(Term::Zero)));
                self.tm(env, z1, z2, &base_ty, v1)?;
                // M[su x/x] scoped in (Γ, x : Nat, y : M), as in reduce.rs.
                let su_x = Term::Succ(Rc::new(Term::Var(LocalVar(1))));
                let step_ty = m1.apply_local(
                    &LocalSubst::id(&env.gamma).shift_local(2).extended(Rc::new(su_x)),
                );
                let e_xy = e_x.push_entry(Rc::clone(m1), v1.clone());
                self.tm(&e_xy, s1, s2, &step_ty, v1)?;
                self.tm_nee(env, n1, n2)?; // inferred Nat: redundant, ignored
                Ok((
                    m1.apply_local(&LocalSubst::id(&env.gamma).extended(Rc::clone(n1))),
                    v1.clone(),
                ))
            }
            // elim_Empty neutral congruence (extension); mirrors ElimNat
            // minus the base/step branches.
            (
                Term::ElimEmpty { level: v1, scrut_level: s1, motive: m1, scrut: n1 },
                Term::ElimEmpty { level: v2, scrut_level: s2, motive: m2, scrut: n2 },
            ) => {
                self.lev_eq(v1, v2)?;
                self.lev_eq(s1, s2)?;
                let e_x = env.push_entry(Rc::new(Type::Empty { level: s1.clone() }), s1.clone());
                self.ty(&e_x, m1, m2, v1)?;
                self.tm_nee(env, n1, n2)?; // inferred Empty: redundant, ignored
                Ok((
                    m1.apply_local(&LocalSubst::id(&env.gamma).extended(Rc::clone(n1))),
                    v1.clone(),
                ))
            }
            // elim_sEmpty neutral congruence (extension) — ElimEmpty's arm
            // with the scrutinees *skipped*: they sit at sEmpty, whose
            // irrelevance arm accepts any two terms, so comparing them
            // would be that arm anyway (docs/sprop-design.md §5.3). The
            // motive instances agree for the same reason.
            (
                Term::ElimSEmpty { level: v1, scrut_level: s1, motive: m1, scrut: n1 },
                Term::ElimSEmpty { level: v2, scrut_level: s2, motive: m2, scrut: _ },
            ) => {
                self.lev_eq(v1, v2)?;
                self.lev_eq(s1, s2)?;
                let e_x =
                    env.push_entry(Rc::new(Type::SEmpty { level: s1.clone() }), s1.clone());
                self.ty(&e_x, m1, m2, v1)?;
                Ok((
                    m1.apply_local(&LocalSubst::id(&env.gamma).extended(Rc::clone(n1))),
                    v1.clone(),
                ))
            }
            // case neutral congruence (extension); mirrors ElimNat — all
            // annotations compared (branches at M[inl x/z] / M[inr y/z]), the
            // scrutinee via tm_nee, result inferred as M[scrut/z]. Fires only
            // on a neutral scrutinee (canonical inl/inr β-fired in reduce).
            (
                Term::Case {
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
                Term::Case {
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
                let lmax = Level::max(dl1.clone(), cl1.clone());
                let sum = Type::Sum {
                    lhs_level: dl1.clone(),
                    rhs_level: cl1.clone(),
                    lhs: Rc::clone(s1),
                    rhs: Rc::clone(t1),
                };
                // M scoped in (Γ, z : A + B), as in typing.rs.
                let e_z = env.push_entry(Rc::new(sum.clone()), lmax.clone());
                self.ty(&e_z, m1, m2, ml1)?;
                // c_l at M[inl x/z] in (Γ, x : A).
                let e_x = env.push_entry(Rc::clone(s1), dl1.clone());
                let inl_x = Term::Inl {
                    lhs_level: dl1.clone(),
                    rhs_level: cl1.clone(),
                    lhs: Rc::new(s1.shift_local(1)),
                    rhs: Rc::new(t1.shift_local(1)),
                    val: Rc::new(Term::Var(LocalVar(0))),
                };
                let left_ty = m1.apply_local(
                    &LocalSubst::id(&env.gamma).shift_local(1).extended(Rc::new(inl_x)),
                );
                self.tm(&e_x, l1, l2, &left_ty, ml1)?;
                // c_r at M[inr y/z] in (Γ, y : B).
                let e_y = env.push_entry(Rc::clone(t1), cl1.clone());
                let inr_y = Term::Inr {
                    lhs_level: dl1.clone(),
                    rhs_level: cl1.clone(),
                    lhs: Rc::new(s1.shift_local(1)),
                    rhs: Rc::new(t1.shift_local(1)),
                    val: Rc::new(Term::Var(LocalVar(0))),
                };
                let right_ty = m1.apply_local(
                    &LocalSubst::id(&env.gamma).shift_local(1).extended(Rc::new(inr_y)),
                );
                self.tm(&e_y, r1, r2, &right_ty, ml1)?;
                self.tm_nee(env, n1, n2)?; // inferred A + B: redundant, ignored
                Ok((
                    m1.apply_local(&LocalSubst::id(&env.gamma).extended(Rc::clone(n1))),
                    ml1.clone(),
                ))
            }
            // elim_W neutral congruence (extension); mirrors ElimNat/Case —
            // all annotations compared (the step at M[sup(a,f)/z] under the
            // (a, f, ih) telescope, as in typing.rs), the scrutinee via
            // tm_nee, result inferred as M[scrut/z]. Fires only on a neutral
            // scrutinee (a canonical sup β-fired in reduce).
            (
                Term::ElimW {
                    shape_level: dl1,
                    pos_level: cl1,
                    motive_level: ml1,
                    shape: s1,
                    pos: t1,
                    motive: m1,
                    step: st1,
                    scrut: n1,
                },
                Term::ElimW {
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
                let e_x = env.push_entry(Rc::clone(s1), dl1.clone());
                self.ty(&e_x, t1, t2, cl1)?;
                let lmax = Level::max(dl1.clone(), cl1.clone());
                let w = Type::W {
                    shape_level: dl1.clone(),
                    pos_level: cl1.clone(),
                    shape: Rc::clone(s1),
                    pos: Rc::clone(t1),
                };
                // M scoped in (Γ, z : W).
                let e_z = env.push_entry(Rc::new(w.clone()), lmax.clone());
                self.ty(&e_z, m1, m2, ml1)?;
                // Steps under (Γ, a : S, f : Π(y:T[a/x]). W,
                // ih : Π(y:T[a/x]). M[f y/z]) at M[sup(a, f)/z] — the same
                // construction as the typing rule.
                let e_a = env.push_entry(Rc::clone(s1), dl1.clone());
                let f_ty = Type::Pi {
                    dom_level: cl1.clone(),
                    cod_level: lmax.clone(),
                    dom: Rc::clone(t1),
                    cod: Rc::new(w.shift_local(2)),
                };
                let e_af =
                    e_a.push_entry(Rc::new(f_ty), Level::max(cl1.clone(), lmax.clone()));
                let f_y = Term::App {
                    fun: Rc::new(Term::Var(LocalVar(1))),
                    dom_level: cl1.clone(),
                    cod_level: lmax.clone(),
                    dom: Rc::new(t1.shift_local(2)),
                    cod: Rc::new(w.shift_local(4)),
                    arg: Rc::new(Term::Var(LocalVar(0))),
                };
                let ih_cod = m1.apply_local(
                    &LocalSubst::id(&env.gamma).shift_local(3).extended(Rc::new(f_y)),
                );
                let ih_ty = Type::Pi {
                    dom_level: cl1.clone(),
                    cod_level: ml1.clone(),
                    dom: Rc::new(t1.shift_local(1)),
                    cod: Rc::new(ih_cod),
                };
                let e_step =
                    e_af.push_entry(Rc::new(ih_ty), Level::max(cl1.clone(), ml1.clone()));
                let Type::W { shape: ws2, pos: wp2, .. } = w.shift_local(2) else {
                    unreachable!()
                };
                let sup_af = Term::Sup {
                    shape_level: dl1.clone(),
                    pos_level: cl1.clone(),
                    shape_ty: ws2,
                    pos_ty: wp2,
                    label: Rc::new(Term::Var(LocalVar(1))),
                    children: Rc::new(Term::Var(LocalVar(0))),
                };
                let step_ty = m1.apply_local(
                    &LocalSubst::id(&env.gamma)
                        .shift_local(3)
                        .extended(Rc::new(sup_af.shift_local(1))),
                );
                self.tm(&e_step, st1, st2, &step_ty, ml1)?;
                self.tm_nee(env, n1, n2)?; // inferred W: redundant, ignored
                Ok((
                    m1.apply_local(&LocalSubst::id(&env.gamma).extended(Rc::clone(n1))),
                    ml1.clone(),
                ))
            }
            // elim_Wf neutral congruence (extension): same shape as elim_W's,
            // with the step telescope taken from `wf_step_telescope` — the
            // single source shared with typing.rs, so the two cannot drift.
            // Fires only on a neutral scrutinee; this is what makes two
            // inductions over the *same* open term convertible.
            (
                Term::ElimWf {
                    level: l1,
                    motive_level: ml1,
                    shape: s1,
                    arity: k1,
                    motive: m1,
                    step: st1,
                    scrut: n1,
                },
                Term::ElimWf {
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
                let e_x = env.push_entry(Rc::clone(s1), l1.clone());
                self.tm(&e_x, k1, k2, &Type::Nat, &Level::Zero)?;
                let wf = Type::Wf {
                    level: l1.clone(),
                    shape: Rc::clone(s1),
                    arity: Rc::clone(k1),
                };
                let e_z = env.push_entry(Rc::new(wf), l1.clone());
                self.ty(&e_z, m1, m2, ml1)?;
                let (cs_ty, ih_ty, step_ty) =
                    wf_step_telescope(&env.gamma, l1, ml1, s1, k1, m1);
                let e_a = env.push_entry(Rc::clone(s1), l1.clone());
                let e_cs = e_a.push_entry(Rc::new(cs_ty), l1.clone());
                let e_step = e_cs.push_entry(Rc::new(ih_ty), ml1.clone());
                self.tm(&e_step, st1, st2, &step_ty, ml1)?;
                self.tm_nee(env, n1, n2)?; // inferred Wf: redundant, ignored
                Ok((
                    m1.apply_local(&LocalSubst::id(&env.gamma).extended(Rc::clone(n1))),
                    ml1.clone(),
                ))
            }
            // J neutral congruence (extension beyond ch. 04); mirrors the
            // ElimNat arm — annotations compared, scrutinee via tm_nee.
            (
                Term::J {
                    ty_level: al1,
                    motive_level: ml1,
                    ty: s1,
                    lhs: a1,
                    motive: m1,
                    case: c1,
                    rhs: r1,
                    proof: p1,
                },
                Term::J {
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
                let e_y = env.push_entry(Rc::clone(s1), al1.clone());
                let p_ty = Type::Id {
                    level: al1.clone(),
                    ty: Rc::new(s1.shift_local(1)),
                    lhs: Rc::new(a1.shift_local(1)),
                    rhs: Rc::new(Term::Var(LocalVar(0))),
                };
                let e_yp = e_y.push_entry(Rc::new(p_ty), al1.clone());
                self.ty(&e_yp, m1, m2, ml1)?;
                let refl_a = Term::Refl {
                    level: al1.clone(),
                    ty: Rc::clone(s1),
                    tm: Rc::clone(a1),
                };
                let case_ty = m1.apply_local(
                    &LocalSubst::id(&env.gamma)
                        .extended(Rc::clone(a1))
                        .extended(Rc::new(refl_a)),
                );
                self.tm(env, c1, c2, &case_ty, ml1)?;
                self.tm(env, r1, r2, s1, al1)?;
                self.tm_nee(env, p1, p2)?; // inferred Id: redundant, ignored
                Ok((
                    m1.apply_local(
                        &LocalSubst::id(&env.gamma)
                            .extended(Rc::clone(r1))
                            .extended(Rc::clone(p1)),
                    ),
                    ml1.clone(),
                ))
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
                Term::Transp {
                    ty_level: al1,
                    motive_level: ml1,
                    ty: s1,
                    motive: m1,
                    lhs: a1,
                    rhs: b1,
                    proof: _,
                    tm: t1,
                },
                Term::Transp {
                    ty_level: al2,
                    motive_level: ml2,
                    ty: s2,
                    motive: m2,
                    lhs: a2,
                    rhs: b2,
                    proof: _,
                    tm: t2,
                },
            ) => {
                self.lev_eq(al1, al2)?;
                self.lev_eq(ml1, ml2)?;
                self.ty(env, s1, s2, al1)?;
                self.tm(env, a1, a2, s1, al1)?;
                self.tm(env, b1, b2, s1, al1)?;
                // P scoped in (Γ, x : I), as in typing.rs.
                let e_x = env.push_entry(Rc::clone(s1), al1.clone());
                self.ty(&e_x, m1, m2, ml1)?;
                let t_ty =
                    m1.apply_local(&LocalSubst::id(&env.gamma).extended(Rc::clone(a1)));
                self.tm(env, t1, t2, &t_ty, ml1)?;
                Ok((
                    m1.apply_local(&LocalSubst::id(&env.gamma).extended(Rc::clone(b1))),
                    ml1.clone(),
                ))
            }
            (
                Term::App { fun: f1, dom_level: dl1, cod_level: cl1, dom: s1, cod: t1, arg: a1 },
                Term::App { fun: f2, dom_level: dl2, cod_level: cl2, dom: s2, cod: t2, arg: a2 },
            ) => {
                self.lev_eq(dl1, dl2)?;
                self.lev_eq(cl1, cl2)?;
                self.ty(env, s1, s2, dl1)?;
                let e_x = env.push_entry(Rc::clone(s1), dl1.clone());
                self.ty(&e_x, t1, t2, cl1)?;
                // The type inferred for the heads is ignored (ch. 06: the
                // annotations of well-typed applications are already forced).
                self.tm_nee(env, f1, f2)?;
                self.tm(env, a1, a2, s1, dl1)?;
                Ok((
                    t1.apply_local(&LocalSubst::id(&env.gamma).extended(Rc::clone(a1))),
                    cl1.clone(),
                ))
            }
            // fst/snd neutral congruence (extension; mirrors App — the Σ
            // annotations forced by well-typedness are compared, the pair via
            // tm_nee). These arms fire only when the projected pair is itself
            // neutral (η already handled non-neutral pairs in tm_nf).
            (
                Term::Fst { fst_level: dl1, snd_level: cl1, fst_ty: s1, snd_ty: t1, pair: p1 },
                Term::Fst { fst_level: dl2, snd_level: cl2, fst_ty: s2, snd_ty: t2, pair: p2 },
            ) => {
                self.lev_eq(dl1, dl2)?;
                self.lev_eq(cl1, cl2)?;
                self.ty(env, s1, s2, dl1)?;
                let e_x = env.push_entry(Rc::clone(s1), dl1.clone());
                self.ty(&e_x, t1, t2, cl1)?;
                self.tm_nee(env, p1, p2)?; // inferred Σ: redundant, ignored
                Ok(((**s1).clone(), dl1.clone()))
            }
            (
                Term::Snd { fst_level: dl1, snd_level: cl1, fst_ty: s1, snd_ty: t1, pair: p1 },
                Term::Snd { fst_level: dl2, snd_level: cl2, fst_ty: s2, snd_ty: t2, pair: p2 },
            ) => {
                self.lev_eq(dl1, dl2)?;
                self.lev_eq(cl1, cl2)?;
                self.ty(env, s1, s2, dl1)?;
                let e_x = env.push_entry(Rc::clone(s1), dl1.clone());
                self.ty(&e_x, t1, t2, cl1)?;
                self.tm_nee(env, p1, p2)?;
                let fst_p = Term::Fst {
                    fst_level: dl1.clone(),
                    snd_level: cl1.clone(),
                    fst_ty: Rc::clone(s1),
                    snd_ty: Rc::clone(t1),
                    pair: Rc::clone(p1),
                };
                Ok((
                    t1.apply_local(&LocalSubst::id(&env.gamma).extended(Rc::new(fst_p))),
                    cl1.clone(),
                ))
            }
            (
                Term::UApp { fun: f1, levels: ls1 },
                Term::UApp { fun: f2, levels: ls2 },
            ) => {
                let env = &env.with_layer(Layer::Meta);
                let (w, _) = self.tm_nee(env, f1, f2)?;
                let Type::UPi { num_vars, level, body } = &w else {
                    return Err(NC);
                };
                if ls1.len() != ls2.len() || ls1.len() != *num_vars as usize || ls1.is_empty()
                {
                    return Err(NC);
                }
                for (x, y) in ls1.iter().zip(ls2) {
                    self.lev_eq(x, y)?;
                }
                // Written vectors are outermost-first; instantiation wants
                // innermost-first (as in reduce.rs).
                let phi: Vec<Level> = ls1.iter().rev().cloned().collect();
                Ok((body.inst_univ(&phi), level.inst_at(&phi, 0)))
            }
            (
                Term::CtxApp { fun: f1, ctx: c1 },
                Term::CtxApp { fun: f2, ctx: c2 },
            ) => {
                let env = &env.with_layer(Layer::Meta);
                let (w, _) = self.tm_nee(env, f1, f2)?;
                let Type::CtxPi { level, body } = &w else {
                    return Err(NC);
                };
                self.ctx(env, Layer::Prog, c1, c2)?;
                Ok((
                    body.apply_global(&GlobalSubst::single(GlobalEntry::Ctx(c1.clone()))),
                    level.clone(),
                ))
            }
            (Term::TyApp { fun: f1, arg: t1 }, Term::TyApp { fun: f2, arg: t2 }) => {
                let env = &env.with_layer(Layer::Meta);
                let (w, _) = self.tm_nee(env, f1, f2)?;
                let Type::TyPi { ctx, arg_level, body_level, body } = &w else {
                    return Err(NC);
                };
                let e_d = env.in_ctx(ctx.clone(), Layer::Prog);
                self.ty(&e_d, t1, t2, arg_level)?;
                Ok((
                    body.apply_global(&GlobalSubst::single(GlobalEntry::Ty(Rc::clone(t1)))),
                    body_level.clone(),
                ))
            }
            (
                Term::LetBoxTy {
                    motive_level: ml1, code_level: cl1, ctx: d1, motive: m1, body: b1, scrut: n1,
                },
                Term::LetBoxTy {
                    motive_level: ml2, code_level: cl2, ctx: d2, motive: m2, body: b2, scrut: n2,
                },
            ) => {
                let env = &env.with_layer(Layer::Meta);
                self.lev_eq(ml1, ml2)?;
                self.lev_eq(cl1, cl2)?;
                self.ctx(env, Layer::Prog, d1, d2)?;
                self.tm_nee(env, n1, n2)?; // inferred □(Δ ⊢ Ty l): ignored
                let code_ty = Type::CodeTy { ctx: d1.clone(), level: cl1.clone() };
                let e_x = env.push_entry(Rc::new(code_ty), Level::Zero);
                self.ty(&e_x, m1, m2, ml1)?;
                // Bodies under Ψ, U : Typ_c(Δ, l) at M[box U/x_T].
                let e_u = env.push_global(GlobalBinding::Ty {
                    ctx: d1.clone(),
                    layer: Layer::Code,
                    level: cl1.clone(),
                });
                let box_u = Term::BoxTy(Rc::new(gty(0, &d1.shift_global(1))));
                let body_ty = m1
                    .shift_global(1)
                    .apply_local(&LocalSubst::id(&e_u.gamma).extended(Rc::new(box_u)));
                self.tm(&e_u, b1, b2, &body_ty, ml1)?;
                Ok((
                    m1.apply_local(&LocalSubst::id(&env.gamma).extended(Rc::clone(n1))),
                    ml1.clone(),
                ))
            }
            (
                Term::LetBoxTm {
                    motive_level: ml1, code_level: cl1, ctx: d1, ty: t1, motive: m1,
                    body: b1, scrut: n1,
                },
                Term::LetBoxTm {
                    motive_level: ml2, code_level: cl2, ctx: d2, ty: t2, motive: m2,
                    body: b2, scrut: n2,
                },
            ) => {
                let env = &env.with_layer(Layer::Meta);
                self.lev_eq(ml1, ml2)?;
                self.lev_eq(cl1, cl2)?;
                self.ctx(env, Layer::Prog, d1, d2)?;
                let e_d = env.in_ctx(d1.clone(), Layer::Prog);
                self.ty(&e_d, t1, t2, cl1)?;
                self.tm_nee(env, n1, n2)?; // inferred □(Δ ⊢ T @ l): ignored
                let code_ty = Type::CodeTm {
                    ctx: d1.clone(),
                    ty: Rc::clone(t1),
                    level: cl1.clone(),
                };
                let e_x = env.push_entry(Rc::new(code_ty), Level::Zero);
                self.ty(&e_x, m1, m2, ml1)?;
                // Bodies under Ψ, u : Trm_c(Δ ⊢ T @ l) at M[box u/x_t].
                let e_u = env.push_global(GlobalBinding::Tm {
                    ctx: d1.clone(),
                    layer: Layer::Code,
                    ty: Rc::clone(t1),
                    level: cl1.clone(),
                    body: None,
                });
                let box_u = Term::BoxTm(Rc::new(gtm(0, &d1.shift_global(1))));
                let body_ty = m1
                    .shift_global(1)
                    .apply_local(&LocalSubst::id(&e_u.gamma).extended(Rc::new(box_u)));
                self.tm(&e_u, b1, b2, &body_ty, ml1)?;
                Ok((
                    m1.apply_local(&LocalSubst::id(&env.gamma).extended(Rc::clone(n1))),
                    ml1.clone(),
                ))
            }
            (
                Term::ElimCodeTy {
                    ty_motive_level: al1, tm_motive_level: al2, motives: am, branches: ab,
                    code_level: acl, ctx: actx, scrut: an,
                },
                Term::ElimCodeTy {
                    ty_motive_level: bl1, tm_motive_level: bl2, motives: bm, branches: bb,
                    code_level: bcl, ctx: bctx, scrut: bn,
                },
            ) => {
                let env = &env.with_layer(Layer::Meta);
                self.rec_ca(
                    env,
                    &RecSide { l1: al1, l2: al2, motives: am, branches: ab },
                    &RecSide { l1: bl1, l2: bl2, motives: bm, branches: bb },
                )?;
                self.lev_eq(acl, bcl)?;
                self.ctx(env, Layer::Prog, actx, bctx)?;
                // Blocked on box (U^δ): compared syntactically. Otherwise the
                // scrutinees are neutral.
                match (&**an, &**bn) {
                    (Term::BoxTy(c1), Term::BoxTy(c2)) => {
                        match (&**c1, &**c2) {
                            (Type::GlobalTy { .. }, Type::GlobalTy { .. }) if c1 == c2 => {}
                            _ => return Err(NC),
                        }
                    }
                    (Term::BoxTy(_), _) | (_, Term::BoxTy(_)) => return Err(NC),
                    _ => {
                        self.tm_nee(env, an, bn)?; // inferred □(Δ ⊢ Ty l): ignored
                    }
                }
                Ok((
                    inst_ty_motive(
                        &am.ty_motive,
                        (0, 0, 0),
                        acl.clone(),
                        actx.clone(),
                        (**an).clone(),
                        &env.gamma,
                    ),
                    al1.clone(),
                ))
            }
            (
                Term::ElimCodeTm {
                    ty_motive_level: al1, tm_motive_level: al2, motives: am, branches: ab,
                    code_level: acl, ctx: actx, ty: aty, scrut: an,
                },
                Term::ElimCodeTm {
                    ty_motive_level: bl1, tm_motive_level: bl2, motives: bm, branches: bb,
                    code_level: bcl, ctx: bctx, ty: bty, scrut: bn,
                },
            ) => {
                let env = &env.with_layer(Layer::Meta);
                self.rec_ca(
                    env,
                    &RecSide { l1: al1, l2: al2, motives: am, branches: ab },
                    &RecSide { l1: bl1, l2: bl2, motives: bm, branches: bb },
                )?;
                self.lev_eq(acl, bcl)?;
                self.ctx(env, Layer::Prog, actx, bctx)?;
                let e_d = env.in_ctx(actx.clone(), Layer::Prog);
                self.ty(&e_d, aty, bty, &Level::succ(acl.clone()))?;
                match (&**an, &**bn) {
                    (Term::BoxTm(c1), Term::BoxTm(c2)) => {
                        match (&**c1, &**c2) {
                            (Term::GlobalTm { .. }, Term::GlobalTm { .. }) if c1 == c2 => {}
                            _ => return Err(NC),
                        }
                    }
                    (Term::BoxTm(_), _) | (_, Term::BoxTm(_)) => return Err(NC),
                    _ => {
                        self.tm_nee(env, an, bn)?; // inferred □(Δ ⊢ T @ l): ignored
                    }
                }
                // Conclusion at l₂ (the ch. 04 typing rule; the ch. 06 rule
                // writes l₁, a typo).
                Ok((
                    inst_tm_motive(
                        &am.tm_motive,
                        (0, 0, 0),
                        acl.clone(),
                        actx.clone(),
                        (**aty).clone(),
                        (**an).clone(),
                        &env.gamma,
                    ),
                    al2.clone(),
                ))
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
    fn rec_ca(&mut self, env: &Env, a: &RecSide, b: &RecSide) -> R {
        self.lev_eq(a.l1, b.l1)?;
        self.lev_eq(a.l2, b.l2)?;

        // G_M: the two motives, each under its scope.
        let motive_specs = rec::motive_specs(a.l1, a.l2);
        let ma = rec::motive_types(a.motives);
        let mb = rec::motive_types(b.motives);
        for (spec, (x, y)) in motive_specs.iter().zip(ma.into_iter().zip(mb)) {
            let e = env.push_spec(&spec.tele);
            self.ty(&e, x, y, &spec.level)?;
        }

        // G_Typ G_Trm: the 45 branches, each at its instantiated motive
        // type under its telescope.
        let branch_specs = rec::branch_specs(a.motives, a.l1, a.l2, &env.gamma);
        let ba = rec::branch_terms(a.branches);
        let bb = rec::branch_terms(b.branches);
        for (spec, (x, y)) in branch_specs.iter().zip(ba.into_iter().zip(bb)) {
            let e = env.push_spec(&spec.tele);
            self.tm(&e, x, y, &spec.ty, &spec.level)?;
        }
        Ok(())
    }
}
