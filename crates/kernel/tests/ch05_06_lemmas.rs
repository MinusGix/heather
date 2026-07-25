//! **The ch. 05/06 lemma sweep**: property tests for stated lemmas of DeLaM
//! ch. 05 (*Syntactic Operations and Properties*) and ch. 06 (*Reduction and
//! Convertibility*) that the suite did not machine-check.
//!
//! Motivated by `issues/unit-level-and-vec-preservation.md`: the suite had
//! `conv_properties::reduction_preserves_type`, the **term** half of ch. 06's
//! Preservation lemma, and no type half — which is the only reason
//! `Vec^l(T;0) ⇝ Unit` could drop a level unnoticed from phase 1 of
//! [[wf-former]] to phase 4. *Half a stated lemma is a blind spot shaped
//! exactly like its other half.* This file is the systematic follow-up.
//!
//! The full audit — all 53 lemmas of ch. 05/06, each with its paper location,
//! its kernel counterpart, and a verdict — is `docs/ch05-06-lemma-audit.md`.
//! Every test below cites the lemma it checks by paper file and line.
//!
//! Conventions inherited from the rest of the suite: generated witnesses come
//! from `common/wt.rs` (well-typed) or `common/mod.rs` (well-scoped), and
//! failures report **seeds only** — never Debug-format a kernel term into an
//! assertion message (CLAUDE.md).

mod common;

use std::rc::Rc;

use common::wt::{gen_wt_env, gen_wt_subst, gen_wt_term, gen_wt_type, FUEL};
use common::{gen_scope, gen_sigma, gen_subst, gen_term, law, BaseRef, Rng, Sc, Shape};
use heather_kernel::conv::conv_type;
use heather_kernel::layer::Layer;
use heather_kernel::level::Level;
use heather_kernel::reduce::{
    is_neutral_term, is_neutral_type, is_whnf_term, is_whnf_type, step_term, step_type, whnf_type,
};
use heather_kernel::subst::{GlobalEntry, GlobalSubst};
use heather_kernel::typing::{check_term, check_type, infer_term, TypeError};

const CASES: u64 = 300;
const BUDGET: u32 = 8;

// ==========================================================================
// ch. 06 — Reduction
// ==========================================================================

/// **ch. 06 Soundness** (`06_reduction_and_convertibility.tex:148`), the
/// *type* half: *if `⊢_i T @ l` and `T ⇝ T'` then `⊢_i T ≡ T' @ l`*.
///
/// `conv_properties::conv_relates_term_to_its_whnf` is the term half, and was
/// the only half — the same asymmetry that hid the `Vec` level bug, one lemma
/// earlier in the same chapter. Checked in both orientations, since the
/// algorithm must also be symmetric on well-formed inputs.
#[test]
fn conv_relates_type_to_its_whnf() {
    for seed in 0..CASES {
        let mut r = Rng::new(seed ^ 0x2545f4914f6cdd1d);
        let env = gen_wt_env(&mut r);
        let (ty, l) = gen_wt_type(&env, &mut r, BUDGET);
        let w = whnf_type(&ty, &env.gamma, FUEL)
            .unwrap_or_else(|_| panic!("seed {seed}: well-formed type exhausted whnf fuel"));
        let at = env.layer.type_layer();
        let lr = conv_type(&env.psi, &env.gamma, at, &ty, &w, &l, FUEL);
        assert!(lr.is_ok(), "seed {seed}: T ≢ whnf(T): {lr:?}");
        let rl = conv_type(&env.psi, &env.gamma, at, &w, &ty, &l, FUEL);
        assert!(rl.is_ok(), "seed {seed}: whnf(T) ≢ T: {rl:?}");
    }
}

/// **ch. 06 Determinacy** (`06_…tex:310` and `:319`), the part with content
/// for *this* implementation.
///
/// Both determinacy lemmas hold in the kernel by construction: `step_type` /
/// `step_term` are Rust functions, so a redex has one reduct, and `whnf_*`
/// iterates to a fixed point. What is *not* free — and is exactly what those
/// lemmas presuppose — is that the **normal-form grammar agrees with the
/// step relation**: `W ∪ V` must be precisely the non-stepping types. Get
/// this wrong in one direction and `whnf` returns a term that still reduces
/// (conversion then compares a redex); in the other, `whnf` loops until it
/// burns its fuel.
///
/// This is live territory rather than bookkeeping: `Vec`/`Fin` are normal
/// exactly when their *length* is stuck, so `is_whnf_type` and `step_type`
/// hold two independent copies of that condition (`reduce.rs:1791` vs
/// `:73`), and `ElimCodeTm` is neutral only when its type annotation is
/// already in WHNF.
#[test]
fn whnf_grammar_agrees_with_the_step_relation() {
    for seed in 0..CASES {
        let mut r = Rng::new(seed ^ 0x3c79ac492ba7b653);
        let env = gen_wt_env(&mut r);

        let (ty, _) = gen_wt_type(&env, &mut r, BUDGET);
        let mut cur = (*ty).clone();
        loop {
            let stepped = step_type(&cur, &env.gamma);
            assert_eq!(
                stepped.is_none(),
                is_whnf_type(&cur),
                "seed {seed}: type WHNF grammar disagrees with step"
            );
            // Neutrals are a sub-grammar of the normal forms.
            assert!(
                !is_neutral_type(&cur) || is_whnf_type(&cur),
                "seed {seed}: neutral type is not a normal form"
            );
            match stepped {
                Some(next) => cur = next,
                None => break,
            }
        }

        let (t, _, _) = gen_wt_term(&env, &mut r, BUDGET);
        let mut cur = (*t).clone();
        loop {
            let stepped = step_term(&cur, &env.gamma);
            assert_eq!(
                stepped.is_none(),
                is_whnf_term(&cur),
                "seed {seed}: term WHNF grammar disagrees with step"
            );
            assert!(
                !is_neutral_term(&cur) || is_whnf_term(&cur),
                "seed {seed}: neutral term is not a normal form"
            );
            match stepped {
                Some(next) => cur = next,
                None => break,
            }
        }
    }
}

/// **ch. 06 Local Substitutions** (`06_…tex:289`): *if `⊢_i T @ l`,
/// `T ⇝ T'` and `⊢_i δ : Δ`, then `T[δ] ⇝ T'[δ]`* (and the term half).
///
/// The paper's is a *single-step* statement, and it stays single-step for
/// weak-head reduction: substitution can only unstick a redex whose head is a
/// variable, and such a term does not step in the first place. So a witness
/// where `T[δ]` steps somewhere *else* is a real bug in `subst.rs` or in the
/// binder arithmetic of `reduce.rs` — which is precisely what the `Vec`/`Wf`
/// round touched (lengths and arities are terms substituted at the ambient
/// depth, with no binder of their own).
///
/// `subst_laws.rs` checks the ch. 05 *algebra* of substitutions; this is the
/// ch. 06 side, where substitution meets reduction, and it had nothing.
#[test]
fn reduction_commutes_with_local_substitution() {
    let mut exercised = 0u32;
    for seed in 0..CASES {
        let mut r = Rng::new(seed ^ 0x1d8e4e27c47d124f);
        let env = gen_wt_env(&mut r);
        let target = env.gamma.clone();
        // A well-typed δ : Γ ⊢ Γ, i.e. a random endo-substitution.
        let Some(delta) = gen_wt_subst(&env, &mut r, BUDGET, &target) else { continue };

        let (ty, _) = gen_wt_type(&env, &mut r, BUDGET);
        if let Some(next) = step_type(&ty, &env.gamma) {
            exercised += 1;
            let lhs = step_type(&ty.apply_local(&delta), &env.gamma);
            law!(seed, lhs, Some(next.apply_local(&delta)));
        }

        let (t, _, _) = gen_wt_term(&env, &mut r, BUDGET);
        if let Some(next) = step_term(&t, &env.gamma) {
            exercised += 1;
            let lhs = step_term(&t.apply_local(&delta), &env.gamma);
            law!(seed, lhs, Some(next.apply_local(&delta)));
        }
    }
    assert!(exercised > 20, "only {exercised} reducible witnesses: the law is running vacuously");
}

// ==========================================================================
// ch. 05 — Substitutions
// ==========================================================================

/// **ch. 05 Interactions between Different Substitutions**
/// (`05_syntactic_operations_and_properties_of.tex:438`, `lem:dt:interact`),
/// the three equations `subst_laws.rs` did not have.
///
/// It had the two *term-level* commutations (`T[δ][φ] = T[φ][δ[φ]]` and
/// `T[δ][σ] = T[σ][δ[σ]]`). The lemma also states that the commutation is
/// **functorial in composition** — `(δ ∘ δ')[φ] = δ[φ] ∘ δ'[φ]`, likewise
/// for `σ` — and the `σ`/`φ` interaction `T[σ][φ] = T[φ][σ[φ]]`. Those are
/// the equations the elaborator will lean on when it instantiates a
/// universe-polymorphic global under a local substitution.
#[test]
fn substitution_interactions_are_functorial() {
    for seed in 0..CASES {
        let mut r = Rng::new(seed ^ 0x60bee2bee120fc15);
        let mut sc = gen_scope(&mut r);
        let base = sc.local.base;
        let sh2 = Shape { base, len: r.below(4) };
        let sh1 = Shape { base, len: r.below(4) };

        // δ' : sc.local ⊢ sh1, δ : sh1 ⊢ sh2 — composable as δ ∘ δ'… in the
        // kernel's argument order, `d_outer.compose(d_inner)`.
        let d_outer = {
            let mut s = sc.clone();
            s.local = sh1;
            gen_subst(&s, &mut r, BUDGET, sh2)
        };
        let d_inner = gen_subst(&sc, &mut r, BUDGET, sh1);

        let u0 = r.below(3);
        let sc0 = Sc { univ: u0, globals: vec![], local: Shape { base: BaseRef::Nil, len: 0 } };
        let phi: Vec<Level> = (0..sc.univ).map(|_| common::gen_level(&sc0, &mut r, 2)).collect();
        let (sigma, _) = gen_sigma(&sc, &mut r, BUDGET);

        // (δ ∘ δ')[φ] = δ[φ] ∘ δ'[φ]
        law!(
            seed,
            d_outer.compose(&d_inner).apply_univ(&phi),
            d_outer.apply_univ(&phi).compose(&d_inner.apply_univ(&phi))
        );
        // (δ ∘ δ')[σ] = δ[σ] ∘ δ'[σ]
        law!(
            seed,
            d_outer.compose(&d_inner).apply_global(&sigma),
            d_outer.apply_global(&sigma).compose(&d_inner.apply_global(&sigma))
        );

        // T[σ][φ] = T[φ][σ[φ]] — the σ/φ interaction. `GlobalSubst` has no
        // `apply_univ` of its own (see the audit: the kernel implements no
        // action *on* σ and no σ ∘ σ'), so the componentwise action is
        // spelled out here, which is what the equation says it is.
        sc.local = sh2;
        let t = gen_term(&sc, &mut r, BUDGET);
        let sigma_phi = GlobalSubst {
            entries: sigma
                .entries
                .iter()
                .map(|e| match e {
                    GlobalEntry::Ctx(c) => GlobalEntry::Ctx(c.apply_univ(&phi)),
                    GlobalEntry::Ty(ty) => GlobalEntry::Ty(Rc::new(ty.apply_univ(&phi))),
                    GlobalEntry::Tm(tm) => GlobalEntry::Tm(Rc::new(tm.apply_univ(&phi))),
                })
                .collect(),
        };
        law!(
            seed,
            t.apply_global(&sigma).apply_univ(&phi),
            t.apply_univ(&phi).apply_global(&sigma_phi)
        );
    }
}

// ==========================================================================
// ch. 05 — Typing under substitution and layers
// ==========================================================================

/// **ch. 05 Universe Substitutions** (`05_…tex:589`): *if `⊢_i t : T @ l`
/// and `⊢_L φ : L'`, then `⊢_i t[φ] : T[φ] @ l[φ]`* (and the type half).
///
/// The one substitution lemma whose *typing* consequence the suite never
/// checked in generated form. It is the lemma that the recursor branches
/// live on: a branch binds universe variables (`rec.rs`'s `tele.univs`) and
/// `fire` instantiates them, so a branch whose level bookkeeping is off by a
/// binder violates exactly this statement. It is also the lemma the reverted
/// `Unit`-polymorphism fix was quietly re-interpreting, since `⊢ Unit @ l`
/// for *every* `l` makes `l[φ]` stop being determined by `l`.
#[test]
fn universe_substitution_preserves_typing() {
    let mut exercised = 0u32;
    for seed in 0..CASES {
        let mut r = Rng::new(seed ^ 0x27bb2ee687b0b0fd);
        let env = gen_wt_env(&mut r);
        if env.univs == 0 {
            continue;
        }
        // φ : L ⊢ L', instantiating every ambient universe variable by a
        // closed level (so the image scope has no universe variables).
        let sc0 = Sc { univ: 0, globals: vec![], local: Shape { base: BaseRef::Nil, len: 0 } };
        let phi: Vec<Level> =
            (0..env.univs).map(|_| common::gen_level(&sc0, &mut r, 2)).collect();

        // Every Ψ shape `gen_wt_env` builds is universe-closed (all levels
        // are `0`, all contexts are bare `g`), so `Ψ[φ] = Ψ` and the image
        // scope genuinely has no universe variables left.
        let gamma_p = env.gamma.apply_univ(&phi);
        let (ty, l) = gen_wt_type(&env, &mut r, BUDGET);
        let res = check_type(
            &env.psi,
            0,
            env.layer,
            &gamma_p,
            &ty.apply_univ(&phi),
            &l.subst(&phi),
            FUEL,
        );
        assert!(res.is_ok(), "seed {seed}: T[φ] ill-formed at l[φ]: {res:?}");
        exercised += 1;

        let (t, tty, tl) = gen_wt_term(&env, &mut r, BUDGET);
        let res = check_term(
            &env.psi,
            0,
            env.layer,
            &gamma_p,
            &t.apply_univ(&phi),
            &tty.apply_univ(&phi),
            &tl.subst(&phi),
            FUEL,
        );
        assert!(res.is_ok(), "seed {seed}: t[φ] ill-typed at T[φ]: {res:?}");
    }
    assert!(exercised > 20, "only {exercised} witnesses with universe variables");
}

/// **ch. 05 Local Substitutions** (`05_…tex:716`): *if `⊢_i T @ l` in `Γ'`
/// and `⊢_i δ : Γ'`, then `⊢_i T[δ] @ l`* (and the term half).
///
/// The central substitution lemma. `typing.rs::local_substitutions` is a
/// hand-written instance of it; there was no generated-witness version, so
/// nothing checked it against the formers added in phases 1–3, whose
/// substitution arms are the ones with unusual binder depths (`Wf`'s arity
/// binds one, its motive one, its step three).
#[test]
fn local_substitution_preserves_typing() {
    let mut exercised = 0u32;
    for seed in 0..CASES {
        let mut r = Rng::new(seed ^ 0x6956abd6ed268a3d);
        let env = gen_wt_env(&mut r);
        let target = env.gamma.clone();
        let Some(delta) = gen_wt_subst(&env, &mut r, BUDGET, &target) else { continue };
        exercised += 1;

        let (ty, l) = gen_wt_type(&env, &mut r, BUDGET);
        let res = check_type(
            &env.psi,
            env.univs,
            env.layer,
            &env.gamma,
            &ty.apply_local(&delta),
            &l,
            FUEL,
        );
        assert!(res.is_ok(), "seed {seed}: T[δ] ill-formed: {res:?}");

        let (t, tty, tl) = gen_wt_term(&env, &mut r, BUDGET);
        let res = check_term(
            &env.psi,
            env.univs,
            env.layer,
            &env.gamma,
            &t.apply_local(&delta),
            &tty.apply_local(&delta),
            &tl,
            FUEL,
        );
        assert!(res.is_ok(), "seed {seed}: t[δ] ill-typed at T[δ]: {res:?}");
    }
    assert!(exercised > 20, "only {exercised} substitutions generated");
}

/// **ch. 05 Lifting** (`05_…tex:996`, `lem:dt:lift`): *if `i ≤ i'` and
/// `⊢_i t : T @ l`, then `⊢_{i'} t : T @ l`* — typing is monotone in the
/// layer order `v < c < p < m`.
///
/// Layer gates are the kernel's most-edited invariant: phase 1 of
/// [[wf-former]] gated `Vec`/`Fin`/`Wf` out of layer `c`, phase 3 deleted the
/// gate outright. A gate that rejects at `p` what it accepts at `c` — the
/// easy direction to get backwards — violates this lemma, and until now
/// nothing would have said so.
#[test]
fn typing_is_monotone_in_the_layer() {
    for seed in 0..CASES {
        let mut r = Rng::new(seed ^ 0x4cf5ad432745937f);
        let mut env = gen_wt_env(&mut r);
        env.layer = Layer::Prog;
        env.gamma = common::wt::gen_wt_ctx(&env, &mut r, 4, Layer::Prog);

        let (ty, l) = gen_wt_type(&env, &mut r, BUDGET);
        let res = check_type(&env.psi, env.univs, Layer::Meta, &env.gamma, &ty, &l, FUEL);
        assert!(res.is_ok(), "seed {seed}: ⊢_p T @ l but not ⊢_m: {res:?}");

        let (t, tty, tl) = gen_wt_term(&env, &mut r, BUDGET);
        let res = check_term(&env.psi, env.univs, Layer::Meta, &env.gamma, &t, &tty, &tl, FUEL);
        assert!(res.is_ok(), "seed {seed}: ⊢_p t : T but not ⊢_m: {res:?}");
    }
}

// ==========================================================================
// ch. 05 — Presupposition
// ==========================================================================

/// **ch. 05 Presupposition** (`05_…tex:1446`): *if `⊢_i t : T @ l`, then
/// `⊢_{typeof(i)} T @ l`* — the type a term is given is itself well-formed,
/// at the level it is given at.
///
/// The kernel's inference mode is where this bites: `infer_term` **produces**
/// a `(T, l)` pair, and nothing checked that its own output satisfies the
/// checker. That is the same shape of blind spot as the missing half of
/// Preservation — a judgment the implementation emits but never re-reads.
/// `box` is checking-only and correctly reports `NotInferable`; skipped, the
/// same narrow skip `conv_properties` already uses.
#[test]
fn inferred_types_are_well_formed() {
    let mut exercised = 0u32;
    for seed in 0..CASES {
        let mut r = Rng::new(seed ^ 0x1c8e4d2a9f3b7c61);
        let env = gen_wt_env(&mut r);
        let (t, _, _) = gen_wt_term(&env, &mut r, BUDGET);
        let inferred = infer_term(&env.psi, env.univs, env.layer, &env.gamma, &t, FUEL);
        let Ok((ty, l)) = inferred else {
            // Checking-only forms (`box`) are not inferable by design.
            assert_eq!(
                inferred.unwrap_err(),
                TypeError::NotInferable,
                "seed {seed}: well-typed term failed inference for the wrong reason"
            );
            continue;
        };
        exercised += 1;
        let res = check_type(
            &env.psi,
            env.univs,
            env.layer.type_layer(),
            &env.gamma,
            &ty,
            &l,
            FUEL,
        );
        assert!(res.is_ok(), "seed {seed}: inferred type is not well-formed: {res:?}");
    }
    assert!(exercised > 100, "only {exercised} inferable witnesses");
}

/// A companion to the above at the type level, and the property the reverted
/// fix in `issues/unit-level-and-vec-preservation.md` broke: **inference and
/// checking agree**. If `⊢ T @ l` is inferable, then the inferred level is
/// the *only* level `T` checks at.
///
/// `vec_fin.rs::every_type_has_exactly_one_level` pins this for a hand-built
/// family; this is the generated version, and it is what any candidate fix
/// for the `Vec` gap has to keep passing. Deliberately *not* a statement of
/// the paper — it is the implementation-side reading of ch. 04
/// §Non-cumumulativity's "each term has a unique type", which the audit doc
/// records as a design constraint rather than a lemma.
#[test]
fn inferred_level_is_the_only_level() {
    for seed in 0..CASES {
        let mut r = Rng::new(seed ^ 0x7f4a7c15e3779b9d);
        let env = gen_wt_env(&mut r);
        let (ty, l) = gen_wt_type(&env, &mut r, BUDGET);
        let others = [Level::Zero, Level::succ(l.clone()), Level::succ(Level::succ(l.clone()))];
        for other in others {
            if other.equiv(&l) {
                continue;
            }
            let res =
                check_type(&env.psi, env.univs, env.layer, &env.gamma, &ty, &other, FUEL);
            assert!(
                res.is_err(),
                "seed {seed}: a type checked at two inequivalent levels"
            );
        }
    }
}

// ==========================================================================
// The oracle itself
// ==========================================================================

/// Not a lemma of the paper — a property of the **suite**, and the sweep's
/// own finding.
///
/// Every property test in this crate presupposes that `gen_wt_term` produces
/// well-typed terms. That presupposition is checked by exactly one test,
/// `conv_properties::generated_terms_type_check`, at 300 cases on a single
/// seed stream. When this sweep's `inferred_types_are_well_formed` ran a
/// *different* stream, it found an ill-typed witness at its seed 152 — a
/// rate of about 1 in 3000, which 300 cases on one stream will essentially
/// never see.
///
/// The defect: `TyPi` binds its global type variable at layer `p` and the
/// kernel fixes that (`typing.rs:575`), so a `TyPi`-bound `U` may never be
/// named at layer `c`. The generator built the `Δ` of a contextual type at
/// layer `p`, so `Δ` could contain `U^δ` — and then a layer-`c` body
/// generated in `Δ` could lift that entry type into an annotation (a `J`
/// motive, in the witness), which is ill-formed at `c`. Fixed by generating
/// every `Δ` that hosts a layer-`c` body at layer `c`; such a `Δ` is still a
/// valid layer-`p` context by ch. 05's Lifting lemma, which
/// `typing_is_monotone_in_the_layer` above now checks.
///
/// This test is the widened observer: several independent streams, so a
/// defect at one-in-a-few-thousand cannot hide behind a single seed schedule.
#[test]
fn the_generator_oracle_holds_across_seed_streams() {
    const STREAMS: [u64; 4] = [
        0x1c8e4d2a9f3b7c61,
        0xcbf29ce484222325,
        0x9ae16a3b2f90404f,
        0x2545f4914f6cdd1d,
    ];
    for mix in STREAMS {
        for seed in 0..800u64 {
            let mut r = Rng::new(seed ^ mix);
            let env = gen_wt_env(&mut r);
            let (t, ty, l) = gen_wt_term(&env, &mut r, BUDGET);
            let res =
                check_term(&env.psi, env.univs, env.layer, &env.gamma, &t, &ty, &l, FUEL);
            assert!(
                res.is_ok(),
                "stream {mix:#x} seed {seed}: generator produced an ill-typed term: {res:?}"
            );
        }
    }
}
