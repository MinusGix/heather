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

use std::sync::Arc as Rc;

use common::wt::{gen_wt_env_at as gen_wt_env, gen_wt_subst, gen_wt_term, gen_wt_type, FUEL};
use common::{gen_scope, gen_sigma, gen_subst, gen_term, law, BaseRef, Rng, Sc, Shape};
use heather_kernel::conv::conv_type;
use heather_kernel::layer::Layer;
use heather_kernel::level::Level;
use heather_kernel::reduce::{
    is_neutral_term, is_neutral_type, is_whnf_term, is_whnf_type, whnf_type,
};
use heather_kernel::subst::{GlobalEntry, GlobalSubst};
use heather_kernel::term::{LocalCtx, Term, Type};

/// The single-step relation, for terms far inside the frame budget.
fn step_term(t: &Term, gamma: &LocalCtx) -> Option<Term> {
    heather_kernel::reduce::step_term(t, gamma).expect("a test term steps within the frame budget")
}

/// The single-step relation, for types far inside the frame budget.
fn step_type(t: &Type, gamma: &LocalCtx) -> Option<Type> {
    heather_kernel::reduce::step_type(t, gamma).expect("a test type steps within the frame budget")
}
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
        // **Substitution is a second trigger for the box synthesis gap**
        // (`issues/box-synthesis-gap.md`), and the first one found outside
        // reduction. `δ` can replace a variable sitting in an *inference*
        // position by a payload containing a bare `box` — here
        // `Λ g. box ⟨⟩` under a `capp` head — and `box` is the kernel's one
        // checking-only form. The declarative lemma holds; the bidirectional
        // algorithm is incomplete exactly there. Same narrow skip, and the
        // same reason, as `conv_properties::reduction_preserves_type`.
        if res == Err(TypeError::NotInferable) {
            continue;
        }
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
    let before = heather_kernel::stats::snapshot();
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
    // Coverage, not correctness — and the reason it is an assertion rather
    // than a comment: a generator that stops producing the checked spellings
    // (docs/intro-by-type-design.md) makes every property test in this crate
    // silently vacuous on them, which is exactly how a form gets added and
    // never exercised. `intro_at_nodes` is bumped by the typing rules, so
    // this counts the `@` forms the *checker* met, not the ones the generator
    // built and then discarded.
    let met = heather_kernel::stats::snapshot().since(&before).intro_at_nodes;
    eprintln!("checked spellings met by the checker: {met}");
    assert!(
        met > 0,
        "the generator reached no checked spelling in {} cases — cases 27-31 of \
         `gen_wt_term` are unreachable or always `continue`",
        STREAMS.len() * 800
    );
}

// ==========================================================================
// ch. 05 — Static Code
// ==========================================================================

/// **ch. 05 Static Code** (`05_…tex:1055`, `lem:dt:static`): at layers `v`
/// and `c`, equivalence *is* equality —
///
/// > `⊢_i T ≡ T' @ l` ⇒ `T = T'`; `⊢_i t ≡ t' : T @ l` ⇒ `t = t'`
/// > … *All equalities above are quotient over the equivalence of universe
/// > levels.*
///
/// and the paper spells out the quotient it means:
///
/// > *For example, `Ty (ℓ ⊔ ℓ')` and `Ty (ℓ' ⊔ ℓ)` as code are considered
/// > **equal**, though their universe levels are not exactly syntactically
/// > identical.*
///
/// The kernel has no layer-`c` equivalence judgment — `conv_*` asserts
/// `layer.computes()` — so the implementation-side reading is the lemma's
/// *consequence*: `box` is intensional, and the equality it uses for boxed
/// code must be exactly this quotient. Both directions matter, and they fail
/// in opposite ways: too coarse and `box` stops being intensional (the code
/// eliminator's whole point); too fine and the checker rejects code the
/// declarative system equates, contradicting ch. 08's Convertibility theorem
/// (`08:229`).
///
/// **This test found the kernel on the too-fine side.** `conv.rs` compared
/// boxed code with plain `==`, which rejects the paper's own example
/// verbatim. Fixed first by a `normalize_levels` rewrite before comparing,
/// and now by construction: levels are canonical (`level.rs`,
/// `issues/kernel-compact-level.md`), so the two spellings are one value and
/// `==` is the quotient. The negatives below pin that it did not go too far.
#[test]
fn code_equality_is_equality_modulo_level_equivalence() {
    use heather_kernel::conv::conv_term;
    use heather_kernel::level::UnivVar;
    use heather_kernel::term::{GlobalCtx, LocalCtx};


    let psi = GlobalCtx::default();
    let g = LocalCtx::nil();
    let l0 = Level::Var(UnivVar(0));
    let l1 = Level::Var(UnivVar(1));

    // Both orientations, at a code-of-types type and a code-of-terms type.
    let probe = |a: Term, b: Term, ty: Type, want_ok: bool, what: &str| {
        for (x, y) in [(&a, &b), (&b, &a)] {
            let ck = check_term(&psi, 2, Layer::Meta, &g, x, &ty, &Level::Zero, FUEL);
            assert!(ck.is_ok(), "{what}: side is ill-typed, so the test is vacuous: {ck:?}");
            let got = conv_term(&psi, &g, Layer::Meta, x, y, &ty, &Level::Zero, FUEL);
            assert_eq!(got.is_ok(), want_ok, "{what}: conv gave {got:?}");
        }
    };

    // -- equal modulo levels: must be accepted -----------------------------

    // The paper's example, as code of a type.
    let (ab, ba) = (Level::max(l0.clone(), l1.clone()), Level::max(l1.clone(), l0.clone()));
    probe(
        Term::BoxTy(Rc::new(Type::Ty(ab.clone()))),
        Term::BoxTy(Rc::new(Type::Ty(ba.clone()))),
        Type::CodeTy { ctx: g.clone(), level: Level::succ(ab.clone()) },
        true,
        "Ty(ℓ⊔ℓ') vs Ty(ℓ'⊔ℓ) as code of a type",
    );
    // …and as code of a term, which is what `lem:dt:static` literally says.
    probe(
        Term::BoxTm(Rc::new(Term::TmTy(ab.clone()))),
        Term::BoxTm(Rc::new(Term::TmTy(ba.clone()))),
        Type::CodeTm {
            ctx: g.clone(),
            ty: Rc::new(Type::Ty(Level::succ(ab.clone()))),
            level: Level::succ(Level::succ(ab.clone())),
        },
        true,
        "TmTy(ℓ⊔ℓ') vs TmTy(ℓ'⊔ℓ) as code of a term",
    );
    // Idempotence and unit, the other two monoid laws of the level lattice.
    probe(
        Term::BoxTy(Rc::new(Type::Ty(l0.clone()))),
        Term::BoxTy(Rc::new(Type::Ty(Level::max(l0.clone(), l0.clone())))),
        Type::CodeTy { ctx: g.clone(), level: Level::succ(l0.clone()) },
        true,
        "Ty ℓ vs Ty (ℓ⊔ℓ)",
    );
    probe(
        Term::BoxTy(Rc::new(Type::Ty(l0.clone()))),
        Term::BoxTy(Rc::new(Type::Ty(Level::max(l0.clone(), Level::Zero)))),
        Type::CodeTy { ctx: g.clone(), level: Level::succ(l0.clone()) },
        true,
        "Ty ℓ vs Ty (ℓ⊔0)",
    );
    // The quotient must reach *under* a former, not just at the head.
    let pi_at = |l: Level| {
        Type::Pi {
            dom_level: Level::Zero,
            cod_level: Level::succ(l.clone()),
            dom: Rc::new(Type::Nat),
            cod: Rc::new(Type::Ty(l)),
        }
    };
    probe(
        Term::BoxTy(Rc::new(pi_at(ab.clone()))),
        Term::BoxTy(Rc::new(pi_at(ba.clone()))),
        Type::CodeTy { ctx: g.clone(), level: Level::succ(ab.clone()) },
        true,
        "Π(_:Nat). Ty(ℓ⊔ℓ') vs the ℓ'⊔ℓ variant",
    );

    // -- NOT equal: must still be rejected ---------------------------------
    //
    // Note what cannot be tested here, because it cannot be *posed*: a pair
    // of codes at **inequivalent levels but the same code type**. `□(Δ ⊢ Ty l)`
    // fixes `l`, and at layer `c` a type's level is determined by the type
    // (that is uniqueness-of-types, the very property
    // `issues/unit-level-and-vec-preservation.md` is about), so inequivalent
    // levels force inequivalent code types and the two sides never meet at
    // one `conv_term` call. The level-sensitivity of the comparison is
    // therefore carried by the *positive* cases above being exactly the
    // ≈-classes and no coarser — which the negatives below bracket.

    // Different syntax at the same level stays rejected: layer c does not
    // compute, so `El Nat` is not `Nat` as code.
    probe(
        Term::BoxTy(Rc::new(Type::El { level: Level::Zero, tm: Rc::new(Term::TmNat) })),
        Term::BoxTy(Rc::new(Type::Nat)),
        Type::CodeTy { ctx: g.clone(), level: Level::Zero },
        false,
        "box (El Nat) vs box Nat — layer c does not compute",
    );
    // The sharpest one available, and it lands on the open `Vec` gap:
    // `Vec^0(Nat; 0) ⇝ Unit`, so these two are *convertible as types* at
    // layer p and both sit at level 0 — but as code they are different
    // syntax and must stay apart. A level canonicalization that accidentally
    // reduced, or a comparison that fell through to type conversion, would
    // accept this.
    probe(
        Term::BoxTy(Rc::new(Type::Vec {
            level: Level::Zero,
            elem: Rc::new(Type::Nat),
            len: Rc::new(Term::Zero),
        })),
        Term::BoxTy(Rc::new(Type::Unit { level: Level::Zero })),
        Type::CodeTy { ctx: g.clone(), level: Level::Zero },
        false,
        "box (Vec(Nat;0)) vs box Unit — p-convertible, but not equal as code",
    );
}

/// The generated companion to the hand-built family above: for arbitrary
/// well-typed code, a **level-equivalent variant is convertible with it**.
///
/// The variant is produced by `apply_univ` with `φ(ℓᵢ) = ℓᵢ ⊔ ℓᵢ` — a
/// substitution that is the identity up to level equivalence. Levels are
/// canonical by construction (`issues/kernel-compact-level.md`), so the
/// variant must come out *identical*, which is the stronger claim; before
/// that it rewrote every level position to something structurally
/// different and this test checked that conversion still equated them. A
/// code counts as exercised when a non-equivalent substitution
/// (`ℓᵢ ↦ 1 + ℓᵢ`) does move it, i.e. it mentions a level variable.
#[test]
fn level_equivalent_code_is_convertible() {
    use heather_kernel::conv::conv_term;
    use heather_kernel::level::UnivVar;

    let mut exercised = 0u32;
    for seed in 0..CASES {
        let mut r = Rng::new(seed ^ 0x5851f42d4c957f2d);
        let mut env = gen_wt_env(&mut r);
        if env.univs == 0 {
            continue;
        }
        env.layer = Layer::Meta; // `box` is a layer-m form
        let delta = common::wt::gen_wt_ctx(&env, &mut r, 2, Layer::Code);
        let ce = env.in_ctx(delta.clone(), Layer::Code);
        let (code, cty, cl) = gen_wt_term(&ce, &mut r, BUDGET);

        // φ = (ℓ ↦ ℓ ⊔ ℓ): idempotent, so equivalent at every position.
        let phi: Vec<Level> = (0..env.univs)
            .map(|i| {
                let v = Level::Var(UnivVar(i));
                Level::max(v.clone(), v)
            })
            .collect();
        let twin = code.apply_univ(&phi);
        let bumped: Vec<Level> = (0..env.univs).map(|i| Level::succ(Level::Var(UnivVar(i)))).collect();
        if code.apply_univ(&bumped) == *code {
            continue; // no level variable occurred; nothing to compare
        }
        exercised += 1;
        assert!(twin == *code, "seed {seed}: an equivalent universe substitution changed the code's syntax");

        let ty = Type::CodeTm { ctx: delta, ty: cty, level: cl };
        let a = Term::BoxTm(Rc::clone(&code));
        let b = Term::BoxTm(Rc::new(twin));
        // A level-equivalent variant still checks at the *same* code type —
        // itself worth asserting, since `ty_check` compares levels with
        // `lev_eq` throughout and a site using `==` would show up here.
        let ck = check_term(&env.psi, env.univs, env.layer, &env.gamma, &b, &ty, &Level::Zero, FUEL);
        assert!(ck.is_ok(), "seed {seed}: level-equivalent twin is ill-typed: {ck:?}");
        for (x, y) in [(&a, &b), (&b, &a)] {
            let got =
                conv_term(&env.psi, &env.gamma, Layer::Meta, x, y, &ty, &Level::Zero, FUEL);
            assert!(got.is_ok(), "seed {seed}: code ≉ its level-equivalent twin: {got:?}");
        }
    }
    assert!(exercised > 20, "only {exercised} code witnesses mentioning a level");
}
