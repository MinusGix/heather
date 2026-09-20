//! **Differential test: the checker against the checker**
//! (`docs/intro-by-type-design.md` §3.6, and stage 1b's kill criterion).
//!
//! `tests/conv_differential.rs` holds the value machine's *verdict* against
//! the rewriter's for conversion. Stage 1b moved the same seam one level in:
//! the type a typing rule passes to the next is no longer syntax but a
//! **description** — `ITy = Syn | Sel` — and a description is answered by
//! evaluating it, while the thing it describes was previously spelled by
//! `reduce.rs`. This file is the standing evidence that the two agree.
//!
//! The two sides are the *same checker*, differing in one mode bit
//! ([`heather_kernel::typing::oracle`] is `materialize_eagerly`): under it
//! every selection is spelled the instant it would be formed and the five
//! `@` rules view their annotation through the rewriter, so the oracle is
//! the checker as it stood before descriptions existed. Every arm, every
//! premise, every fuel account is shared. What the differential therefore
//! tests is precisely the new thing and nothing else: **that evaluating a
//! description and rewriting it reach the same verdict.**
//!
//! ## What is generated
//!
//! `wt.rs`'s streams with `at_forms` on, i.e. with the five checked
//! spellings in the generator. Two shapes matter and both are covered:
//!
//! - **`@` forms over component-form children** — `wt.rs`'s synthesis arms,
//!   whose annotation is `El ⌜Σ…⌝` / `El ⌜+…⌝` so the premise `T ⇝* former`
//!   is exercised in its *non*-reflexive case.
//! - **`@` forms that nest** — `wt.rs`'s intro-directed descent, where a
//!   `pair@`'s field is itself a `pair@` (so a description is converted
//!   against an annotation) — and [`nested_projection_chains`], which builds
//!   `fst@` of `snd@` of `pair@` by hand, because no generator arm produces
//!   a projection over a projection and that is exactly where a `Sel` chain
//!   of length > 1 forms.
//!
//! Every stream runs twice, over Ψ and over [`opaque`]'s body-stripped copy
//! of it: the descriptions' evaluation is δ-transparent by construction and
//! the rewriter's whnf is too, so a δ disagreement would be a real one.
//!
//! ## The one asymmetry that is allowed
//!
//! Fuel, for `conv_differential.rs`'s reason: the two spend different
//! amounts, and `OutOfFuel` from either side is "no answer offered", never a
//! disagreement. [`fuel_never_flips_a_verdict`] is what keeps that
//! non-vacuous.
//!
//! Failures report **seeds only**, per `CLAUDE.md`.

mod common;

use std::sync::Arc as Rc;

use common::wt::{
    gen_wt_ctx, gen_wt_env_at as gen_wt_env, gen_wt_term, gen_wt_term_at, gen_wt_type,
    perturb_conv, FUEL,
};
use common::Rng;
use heather_kernel::layer::Layer;
use heather_kernel::level::Level;
use heather_kernel::term::{
    CtxEntry, GlobalBinding, GlobalCtx, LocalCtx, LocalSubst, Term, Type,
};
use heather_kernel::typing::{
    check_local_ctx, check_term, check_type, infer_term, infer_type, oracle, TypeError,
};

/// Cases per seed stream.
const CASES: u64 = 400;

/// Generator budget — how deep a well-typed term `wt.rs` synthesizes.
const BUDGET: u32 = 8;

type R<T = ()> = Result<T, TypeError>;

/// The two verdicts must agree. Exhaustion on either side is not a verdict
/// and is not a disagreement (see the module docs).
///
/// A *verdict* is `Ok` against `Err`, not the error variant: the two modes
/// can reach the same rejection by different premises (a selection that
/// cannot be evaluated is `NotConvertible`, the spelling of it is
/// `HeadMismatch`), and holding them to one variant would be holding the
/// checker to an error-reporting choice rather than to the judgment. Where
/// the variants do agree — every case this suite has seen — that is
/// reported by [`error_variants_agree_too`] as a separate, softer claim.
#[track_caller]
fn agree<T>(seed: u64, what: &str, lazy: R<T>, eager: R<T>) {
    if lazy.as_ref().err() == Some(&TypeError::OutOfFuel)
        || eager.as_ref().err() == Some(&TypeError::OutOfFuel)
    {
        return;
    }
    assert!(
        lazy.is_ok() == eager.is_ok(),
        "seed {seed}: {what}: TYPING DISAGREEMENT — descriptions said {}, \
         the spelled oracle said {} (terms suppressed on purpose)",
        verdict(&lazy),
        verdict(&eager),
    );
}

fn verdict<T>(r: &R<T>) -> &'static str {
    match r {
        Ok(_) => "well typed",
        Err(TypeError::OutOfFuel) => "out of fuel",
        Err(_) => "ill typed",
    }
}

fn opaque(psi: &GlobalCtx) -> GlobalCtx {
    GlobalCtx::new(
        psi.bindings
            .iter()
            .map(|b| match b {
                GlobalBinding::Tm { ctx, layer, ty, level, .. } => GlobalBinding::Tm {
                    ctx: ctx.clone(),
                    layer: *layer,
                    ty: Rc::clone(ty),
                    level: level.clone(),
                    body: None,
                },
                other => other.clone(),
            })
            .collect(),
    )
}

/// `check_term` both ways, over Ψ and over its δ-opaque copy.
#[allow(clippy::too_many_arguments)]
fn check_tm(
    seed: u64,
    what: &str,
    psi: &GlobalCtx,
    univs: u32,
    layer: Layer,
    gamma: &LocalCtx,
    t: &Term,
    ty: &Type,
    l: &Level,
    fuel: u64,
) {
    for (tag, psi) in [("", psi.clone()), (" [opaque]", opaque(psi))] {
        agree(
            seed,
            &format!("{what}{tag}"),
            check_term(&psi, univs, layer, gamma, t, ty, l, fuel),
            oracle::check_term(&psi, univs, layer, gamma, t, ty, l, fuel),
        );
    }
}

/// `infer_term` both ways. The inferred *types* are compared too where both
/// succeed — under the eager mode a selection comes back spelled, and the
/// two spellings need not be syntactically equal, so the comparison is the
/// one the checker itself would make: each side's answer accepted by the
/// other side's `check_term`.
#[allow(clippy::too_many_arguments)]
fn infer_tm(
    seed: u64,
    what: &str,
    psi: &GlobalCtx,
    univs: u32,
    layer: Layer,
    gamma: &LocalCtx,
    t: &Term,
    fuel: u64,
) {
    for (tag, psi) in [("", psi.clone()), (" [opaque]", opaque(psi))] {
        let lazy = infer_term(&psi, univs, layer, gamma, t, fuel);
        let eager = oracle::infer_term(&psi, univs, layer, gamma, t, fuel);
        agree(seed, &format!("{what}{tag}"), lazy.clone(), eager.clone());
        let (Ok((lt, ll)), Ok((et, el))) = (&lazy, &eager) else { continue };
        assert!(ll.equiv(el), "seed {seed}: {what}{tag}: inferred levels differ");
        agree(
            seed,
            &format!("{what}{tag}: lazy's type accepts the term, eagerly"),
            Ok(()),
            oracle::check_term(&psi, univs, layer, gamma, t, lt, ll, fuel),
        );
        agree(
            seed,
            &format!("{what}{tag}: eager's type accepts the term, lazily"),
            Ok(()),
            check_term(&psi, univs, layer, gamma, t, et, el, fuel),
        );
    }
}

fn check_ty(
    seed: u64,
    what: &str,
    psi: &GlobalCtx,
    univs: u32,
    layer: Layer,
    gamma: &LocalCtx,
    ty: &Type,
    l: &Level,
) {
    for (tag, psi) in [("", psi.clone()), (" [opaque]", opaque(psi))] {
        agree(
            seed,
            &format!("{what}{tag}"),
            check_type(&psi, univs, layer, gamma, ty, l, FUEL),
            oracle::check_type(&psi, univs, layer, gamma, ty, l, FUEL),
        );
        agree(
            seed,
            &format!("{what}{tag}: level"),
            infer_type(&psi, univs, layer, gamma, ty, FUEL),
            oracle::infer_type(&psi, univs, layer, gamma, ty, FUEL),
        );
    }
}

// ---------------------------------------------------------------------------
// Stream 1: synthesized triples — the rule that produced them, both ways
// ---------------------------------------------------------------------------

#[test]
fn stream1_synthesized_terms() {
    for seed in 0..CASES {
        let mut r = Rng::new(seed ^ 0x9e3779b97f4a7c15);
        let env = gen_wt_env(&mut r);
        let (t, ty, l) = gen_wt_term(&env, &mut r, BUDGET);
        check_tm(
            seed, "t : T", &env.psi, env.univs, env.layer, &env.gamma, &t, &ty, &l, FUEL,
        );
        infer_tm(seed, "infer t", &env.psi, env.univs, env.layer, &env.gamma, &t, FUEL);
        check_ty(seed, "T @ l", &env.psi, env.univs, env.layer, &env.gamma, &ty, &l);
    }
}

// ---------------------------------------------------------------------------
// Stream 2: a negative control — the perturbed term must be refused by both
// ---------------------------------------------------------------------------

#[test]
fn stream2_perturbed_terms_are_refused_by_both() {
    let mut refusals = 0u64;
    for seed in 0..CASES {
        let mut r = Rng::new(seed ^ 0x2545f4914f6cdd1d);
        let env = gen_wt_env(&mut r);
        let (t, ty, l) = gen_wt_term(&env, &mut r, BUDGET);
        let Some(p) = perturb_conv(&env, &mut r, &t, &ty, &l) else { continue };
        check_tm(
            seed,
            "perturb(t) : T",
            &env.psi,
            env.univs,
            env.layer,
            &env.gamma,
            &p,
            &ty,
            &l,
            FUEL,
        );
        // The perturbation is a *conversion* perturbation — it stays well
        // typed often enough that counting its refusals is not a control.
        // The control is the wrong expected type, which every well-typed
        // term must be refused at, in both modes.
        let wrong = Type::Unit { level: Level::Zero };
        check_tm(
            seed,
            "t at Unit⁰",
            &env.psi,
            env.univs,
            env.layer,
            &env.gamma,
            &t,
            &wrong,
            &Level::Zero,
            FUEL,
        );
        if check_term(
            &env.psi, env.univs, env.layer, &env.gamma, &t, &wrong, &Level::Zero, FUEL,
        )
        .is_err()
        {
            refusals += 1;
        }
    }
    // The stream is only a control if it refuses something: a negative case
    // both modes accept proves nothing about either.
    assert!(refusals > 0, "nothing was refused — the negative control is vacuous");
}

// ---------------------------------------------------------------------------
// Stream 3: open terms in a non-empty Γ, at a *checked* type
// ---------------------------------------------------------------------------
//
// This is where `Sel::Dom` / `Sel::Cod` can form: a λ checked against the
// first component of an un-reduced Σ.

#[test]
fn stream3_open_terms_and_contexts() {
    for seed in 0..CASES {
        let mut r = Rng::new(seed ^ 0xc3a5c85c97cb3127);
        let mut env = gen_wt_env(&mut r);
        env.gamma = gen_wt_ctx(&env, &mut r, 4, env.layer);
        if env.gamma.entries.is_empty() {
            env.gamma.entries.push(CtxEntry { ty: Rc::new(Type::Nat), level: Level::Zero });
        }
        let (ty, l) = gen_wt_type(&env, &mut r, BUDGET / 2);
        let Some(t) = gen_wt_term_at(&env, &mut r, BUDGET, &ty, &l) else { continue };
        check_tm(
            seed, "open t : T", &env.psi, env.univs, env.layer, &env.gamma, &t, &ty, &l,
            FUEL,
        );
        infer_tm(seed, "infer open t", &env.psi, env.univs, env.layer, &env.gamma, &t, FUEL);
        check_ty(seed, "open T @ l", &env.psi, env.univs, env.layer, &env.gamma, &ty, &l);
        for (tag, psi) in [("", env.psi.clone()), (" [opaque]", opaque(&env.psi))] {
            agree(
                seed,
                &format!("ctx wf{tag}"),
                check_local_ctx(&psi, env.univs, env.layer, &env.gamma, FUEL),
                oracle::check_local_ctx(&psi, env.univs, env.layer, &env.gamma, FUEL),
            );
        }
    }
}

// ---------------------------------------------------------------------------
// Stream 4: `@` forms that nest, by hand
// ---------------------------------------------------------------------------

/// `El ⌜·⌝` of an encoding — one decode between the annotation and its
/// former, so the premise `T ⇝* Σ` is never reflexive.
fn el(tm: Term, level: Level) -> Type {
    Type::El { level, tm: Rc::new(tm) }
}

fn enc_nat() -> Term {
    Term::TmNat
}

/// `⌜Σ(x : A). B⌝` with both components non-dependent encodings.
fn enc_sigma(a: Term, b: Term) -> Term {
    Term::TmSigma {
        fst_level: Level::Zero,
        snd_level: Level::Zero,
        fst: Rc::new(a),
        snd: Rc::new(b),
    }
}

/// Towers of `pair@` and chains of `fst@`/`snd@` over them: the shape no
/// generator arm reaches, and the only one that forms a `Sel` chain deeper
/// than one link.
///
/// `Σ(x:Nat). Σ(y:Nat). Nat`, behind a decode at every layer, so that
/// `fst@(U; snd@(T; p))` has to evaluate a description *of* a description.
#[test]
fn nested_projection_chains() {
    let psi = GlobalCtx::new(vec![]);
    let gamma = LocalCtx::nil();
    let inner_code = enc_sigma(enc_nat(), enc_nat());
    let outer_code = enc_sigma(enc_nat(), inner_code.clone());
    let inner = el(inner_code, Level::Zero);
    let outer = el(outer_code, Level::Zero);
    let nat = Type::Nat;
    let zero = Rc::new(Term::Zero);

    // `pair@(T; 0; pair@(U; 0; 0))` — an `@` intro whose field is an `@`
    // intro, i.e. a `pair@` checked against `Sel { T, Snd(0) }`.
    let inner_pair = Rc::new(Term::PairAt {
        ty: Rc::new(inner.clone()),
        fst: Rc::clone(&zero),
        snd: Rc::clone(&zero),
    });
    let pair = Rc::new(Term::PairAt {
        ty: Rc::new(outer.clone()),
        fst: Rc::clone(&zero),
        snd: Rc::clone(&inner_pair),
    });

    // The projection chains over it. `snd@(T; p) : U[fst@(T;p)/x]`, which is
    // `inner` since nothing here is dependent; `fst@`/`snd@` of *that* is
    // the length-2 chain.
    let snd_p = Rc::new(Term::SndAt { ty: Rc::new(outer.clone()), pair: Rc::clone(&pair) });
    let fst_of_snd =
        Rc::new(Term::FstAt { ty: Rc::new(inner.clone()), pair: Rc::clone(&snd_p) });
    let snd_of_snd =
        Rc::new(Term::SndAt { ty: Rc::new(inner.clone()), pair: Rc::clone(&snd_p) });
    // And one more link: a `pair@` whose field is the projection chain.
    let pair_of_proj = Rc::new(Term::PairAt {
        ty: Rc::new(inner.clone()),
        fst: Rc::clone(&fst_of_snd),
        snd: Rc::clone(&snd_of_snd),
    });

    let cases: [(&str, Rc<Term>, Type); 6] = [
        ("pair@ of pair@", Rc::clone(&pair), outer.clone()),
        ("snd@ of pair@", Rc::clone(&snd_p), inner.clone()),
        ("fst@ of snd@", Rc::clone(&fst_of_snd), nat.clone()),
        ("snd@ of snd@", Rc::clone(&snd_of_snd), nat.clone()),
        ("pair@ of two chains", Rc::clone(&pair_of_proj), inner.clone()),
        ("fst@ of pair@ of chains", Rc::new(Term::FstAt { ty: Rc::new(inner.clone()), pair: pair_of_proj }), nat.clone()),
    ];

    // The stream is only about descriptions if descriptions are formed:
    // `sel_evals` counts `ITy::Sel` nodes the value machine evaluated, and a
    // chain of length two over an `El`-wrapped Σ must produce several. Read
    // per-thread, which is where `stats` keeps its cells.
    let before = heather_kernel::stats::snapshot();

    for layer in [Layer::Prog, Layer::Meta] {
        for (seed, (what, t, ty)) in cases.iter().enumerate() {
            let seed = seed as u64;
            // Both modes must *accept* these: they are well typed by
            // construction, and a differential that only ever compares two
            // rejections proves nothing.
            assert_eq!(
                check_term(&psi, 0, layer, &gamma, t, ty, &Level::Zero, FUEL),
                Ok(()),
                "{what} at {layer:?} must check",
            );
            check_tm(seed, what, &psi, 0, layer, &gamma, t, ty, &Level::Zero, FUEL);
            infer_tm(seed, what, &psi, 0, layer, &gamma, t, FUEL);
            // A negative control per case: the wrong expected type.
            check_tm(
                seed,
                &format!("{what} at the wrong type"),
                &psi,
                0,
                layer,
                &gamma,
                t,
                &Type::Unit { level: Level::Zero },
                &Level::Zero,
                FUEL,
            );
        }
    }

    let met = heather_kernel::stats::snapshot().since(&before);
    assert!(
        met.intro_at_nodes > 0,
        "the checked spellings were never judged — the stream is vacuous",
    );
    assert!(
        met.sel_evals > 0,
        "no selection was ever evaluated — the descriptions never formed, so this \
         stream compares the oracle against itself",
    );
}

/// A λ checked against a *selection*: the one shape that makes the checker
/// form `Sel::Dom` and `Sel::Cod`. `Σ(f : Nat → Nat). Nat` behind a decode,
/// inhabited by `pair@(T; λx. x; 0)`.
#[test]
fn lambda_checked_against_a_selection() {
    let psi = GlobalCtx::new(vec![]);
    let gamma = LocalCtx::nil();
    let arrow = Term::TmPi {
        dom_level: Level::Zero,
        cod_level: Level::Zero,
        dom: Rc::new(enc_nat()),
        cod: Rc::new(enc_nat()),
    };
    let ty = el(enc_sigma(arrow, enc_nat()), Level::Zero);
    let id = Rc::new(Term::Lam {
        dom_level: Level::Zero,
        cod_level: Level::Zero,
        dom: Rc::new(el(enc_nat(), Level::Zero)),
        body: Rc::new(Term::Var(heather_kernel::term::LocalVar(0))),
    });
    let t = Rc::new(Term::PairAt {
        ty: Rc::new(ty.clone()),
        fst: id,
        snd: Rc::new(Term::Zero),
    });
    assert_eq!(
        check_term(&psi, 0, Layer::Prog, &gamma, &t, &ty, &Level::Zero, FUEL),
        Ok(()),
        "a lambda field of a pair@ is checked at the Fst selection and must be accepted",
    );
    check_tm(0, "λ at a selection", &psi, 0, Layer::Prog, &gamma, &t, &ty, &Level::Zero, FUEL);
    infer_tm(0, "λ at a selection", &psi, 0, Layer::Prog, &gamma, &t, FUEL);
}

// ---------------------------------------------------------------------------
// The fuel sweep
// ---------------------------------------------------------------------------

#[test]
fn fuel_never_flips_a_verdict() {
    for seed in 0..CASES {
        let mut r = Rng::new(seed ^ 0x8ebc6af09c88c6e3);
        let env = gen_wt_env(&mut r);
        let (t, ty, l) = gen_wt_term(&env, &mut r, BUDGET);
        let truth = check_term(&env.psi, env.univs, env.layer, &env.gamma, &t, &ty, &l, FUEL);
        if truth == Err(TypeError::OutOfFuel) {
            continue;
        }
        for fuel in [0, 1, 2, 4, 16, 64, 256, 4096, 1 << 16] {
            check_tm(
                seed,
                &format!("at fuel {fuel}"),
                &env.psi,
                env.univs,
                env.layer,
                &env.gamma,
                &t,
                &ty,
                &l,
                fuel,
            );
            for side in [
                check_term(&env.psi, env.univs, env.layer, &env.gamma, &t, &ty, &l, fuel),
                oracle::check_term(
                    &env.psi, env.univs, env.layer, &env.gamma, &t, &ty, &l, fuel,
                ),
            ] {
                if side != Err(TypeError::OutOfFuel) {
                    assert_eq!(
                        side.is_ok(),
                        truth.is_ok(),
                        "seed {seed}: fuel {fuel} flipped a verdict",
                    );
                }
            }
        }
    }
}

// ---------------------------------------------------------------------------
// The softer claim: the error variants have agreed too, so far
// ---------------------------------------------------------------------------

/// [`agree`] compares `Ok` against `Err` on purpose. This test records the
/// stronger statement that has in fact held on every case the streams
/// generate — the two modes reject for the *same stated reason* — so that a
/// future change which weakens it is seen and decided about, rather than
/// slipping past a comparison that was never looking.
#[test]
fn error_variants_agree_too() {
    for seed in 0..CASES {
        let mut r = Rng::new(seed ^ 0xff51afd7ed558ccd);
        let env = gen_wt_env(&mut r);
        let (t, ty, l) = gen_wt_term(&env, &mut r, BUDGET);
        let Some(p) = perturb_conv(&env, &mut r, &t, &ty, &l) else { continue };
        let lazy = check_term(&env.psi, env.univs, env.layer, &env.gamma, &p, &ty, &l, FUEL);
        let eager =
            oracle::check_term(&env.psi, env.univs, env.layer, &env.gamma, &p, &ty, &l, FUEL);
        if lazy == Err(TypeError::OutOfFuel) || eager == Err(TypeError::OutOfFuel) {
            continue;
        }
        assert_eq!(lazy, eager, "seed {seed}: the two modes differ in the error variant");
    }
}

/// The substitution judgment, which is the one gate whose premises are a
/// loop of `tm_check`s at types computed from earlier steps.
#[test]
fn identity_substitutions_agree() {
    for seed in 0..CASES {
        let mut r = Rng::new(seed ^ 0x94d049bb133111eb);
        let mut env = gen_wt_env(&mut r);
        env.gamma = gen_wt_ctx(&env, &mut r, 4, env.layer);
        let delta = LocalSubst::id(&env.gamma);
        for (tag, psi) in [("", env.psi.clone()), (" [opaque]", opaque(&env.psi))] {
            agree(
                seed,
                &format!("id subst{tag}"),
                heather_kernel::typing::check_local_subst(
                    &psi, env.univs, env.layer, &env.gamma, &delta, &env.gamma, FUEL,
                ),
                oracle::check_local_subst(
                    &psi, env.univs, env.layer, &env.gamma, &delta, &env.gamma, FUEL,
                ),
            );
        }
    }
}
