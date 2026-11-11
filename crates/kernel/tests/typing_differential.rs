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

    // `pair@^{T}(0; pair@(0; 0))` — an `@` intro whose field is an
    // unannotated `@` intro, i.e. a `pair@` checked against `Sel { T, Snd(0) }`
    // with no type of its own, which is what the elaborator writes.
    let inner_pair = Rc::new(Term::PairAt {
        ty: None,
        fst: Rc::clone(&zero),
        snd: Rc::clone(&zero),
    });
    let pair = Rc::new(Term::PairAt {
        ty: Some(Rc::new(outer.clone())),
        fst: Rc::clone(&zero),
        snd: Rc::clone(&inner_pair),
    });

    // The projection chains over it. `snd@(p) : U[fst@(p)/x]`, which is
    // `inner` since nothing here is dependent; `fst@`/`snd@` of *that* is
    // the length-2 chain.
    let snd_p = Rc::new(Term::SndAt { pair: Rc::clone(&pair) });
    let fst_of_snd =
        Rc::new(Term::FstAt { pair: Rc::clone(&snd_p) });
    let snd_of_snd =
        Rc::new(Term::SndAt { pair: Rc::clone(&snd_p) });
    // And one more link: a `pair@` whose field is the projection chain.
    let pair_of_proj = Rc::new(Term::PairAt {
        ty: Some(Rc::new(inner.clone())),
        fst: Rc::clone(&fst_of_snd),
        snd: Rc::clone(&snd_of_snd),
    });

    let cases: [(&str, Rc<Term>, Type); 6] = [
        ("pair@ of pair@", Rc::clone(&pair), outer.clone()),
        ("snd@ of pair@", Rc::clone(&snd_p), inner.clone()),
        ("fst@ of snd@", Rc::clone(&fst_of_snd), nat.clone()),
        ("snd@ of snd@", Rc::clone(&snd_of_snd), nat.clone()),
        ("pair@ of two chains", Rc::clone(&pair_of_proj), inner.clone()),
        ("fst@ of pair@ of chains", Rc::new(Term::FstAt { pair: pair_of_proj }), nat.clone()),
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

/// Long projection spines view every intermediate receiver, including a
/// dependent final tail. An extra projection past that tail must be refused.
#[test]
fn long_projection_spines_agree_with_the_eager_checker() {
    use heather_kernel::term::LocalVar;
    let psi = GlobalCtx::new(vec![]);
    let z = Level::Zero;
    for depth in [1, 4, 16, 32] {
        let final_ty = Type::Sigma {
            fst_level: z.clone(), snd_level: z.clone(), fst: Rc::new(Type::Nat),
            snd: Rc::new(Type::Id {
                level: z.clone(), ty: Rc::new(Type::Nat),
                lhs: Rc::new(Term::Var(LocalVar(0))), rhs: Rc::new(Term::Var(LocalVar(0))),
            }),
        };
        let mut ty = final_ty;
        for _ in 0..depth {
            ty = Type::Sigma {
                fst_level: z.clone(), snd_level: z.clone(),
                fst: Rc::new(Type::Nat), snd: Rc::new(ty.shift_local(1)),
            };
        }
        let gamma = LocalCtx::nil().extended(Rc::new(ty), z.clone());
        let mut term = Rc::new(Term::Var(LocalVar(0)));
        for _ in 0..depth {
            term = Rc::new(Term::SndAt { pair: term });
        }
        let value = Rc::new(Term::FstAt { pair: Rc::clone(&term) });
        let proof = Rc::new(Term::SndAt { pair: term });
        let expected = Type::Id { level: z.clone(), ty: Rc::new(Type::Nat), lhs: Rc::clone(&value), rhs: value };
        let invalid = Term::FstAt { pair: Rc::clone(&proof) };
        for layer in [Layer::Prog, Layer::Meta] {
            assert_eq!(check_term(&psi, 0, layer, &gamma, &proof, &expected, &z, FUEL), Ok(()));
            check_tm(depth as u64, "dependent long projection", &psi, 0, layer, &gamma, &proof, &expected, &z, FUEL);
            infer_tm(depth as u64, "dependent long projection", &psi, 0, layer, &gamma, &proof, FUEL);
            assert!(infer_term(&psi, 0, layer, &gamma, &invalid, FUEL).is_err());
            infer_tm(depth as u64, "projection past a non-Sigma", &psi, 0, layer, &gamma, &invalid, FUEL);
        }
    }
}

/// Describing the type of a record's `k`-th field costs `k` eliminations,
/// not `k²` (`issues/projection-description-quadratic.md`). Each selection
/// down a Σ telescope is instantiated at `fst@` of the receiver so far, and
/// those receivers are one spine: evaluating each instantiation by itself
/// walked the spine from its head every time, on every query that looked at
/// the type. The tail here mentions the field above it, so the last
/// instantiation is forced, through every receiver below it.
#[test]
fn a_projection_spines_description_is_linear_in_its_length() {
    use heather_kernel::term::LocalVar;
    let psi = GlobalCtx::new(vec![]);
    let z = Level::Zero;
    let nat = || Rc::new(Type::Nat);
    let drives = |depth: usize| {
        // Σ(x₁:Nat). … Σ(x_d:Nat). Σ(y:Nat). x_d = y
        let mut ty = Type::Sigma {
            fst_level: z.clone(), snd_level: z.clone(), fst: nat(),
            snd: Rc::new(Type::Id {
                level: z.clone(), ty: nat(),
                lhs: Rc::new(Term::Var(LocalVar(1))), rhs: Rc::new(Term::Var(LocalVar(0))),
            }),
        };
        for _ in 0..depth {
            ty = Type::Sigma { fst_level: z.clone(), snd_level: z.clone(), fst: nat(), snd: Rc::new(ty) };
        }
        let gamma = LocalCtx::nil().extended(Rc::new(ty), z.clone());
        let mut above = Rc::new(Term::Var(LocalVar(0)));
        for _ in 1..depth {
            above = Rc::new(Term::SndAt { pair: above });
        }
        let tail = Rc::new(Term::SndAt { pair: Rc::clone(&above) });
        let proof = Term::SndAt { pair: Rc::clone(&tail) };
        let expected = Type::Id {
            level: z.clone(), ty: nat(),
            lhs: Rc::new(Term::FstAt { pair: above }), rhs: Rc::new(Term::FstAt { pair: tail }),
        };
        let before = heather_kernel::stats::snapshot();
        assert_eq!(check_term(&psi, 0, Layer::Prog, &gamma, &proof, &expected, &z, FUEL), Ok(()));
        // The control: the same proof at the type with its sides swapped,
        // which no reduction makes this one.
        let Type::Id { lhs, rhs, .. } = &expected else { unreachable!() };
        let swapped = Type::Id { level: z.clone(), ty: nat(), lhs: Rc::clone(rhs), rhs: Rc::clone(lhs) };
        assert!(check_term(&psi, 0, Layer::Prog, &gamma, &proof, &swapped, &z, FUEL).is_err());
        heather_kernel::stats::snapshot().since(&before).eval_drives
    };
    let (short, long) = (drives(32), drives(128));
    assert!(short > 0, "no evaluation was counted, so the comparison below says nothing");
    // Four times the fields: linear is 4×, quadratic 16×.
    assert!(
        long < 6 * short,
        "a spine four times as long cost {long} drives against {short}",
    );
}

/// The head of a projection spine that is a variable is described in the
/// scope its entry was formed in, never shifted into this one
/// (`ITy::At`). So the receiver here is neither the innermost entry nor of a
/// closed type: Γ = `n : Nat, p : Σ(x:Nat). x = n, z : Nat`, and `snd@(p)`
/// proves `fst@(p) = n`. The controls name the entry on either side of `n`
/// instead, which is what a description read one scope off would accept.
#[test]
fn a_projected_variables_type_is_read_in_its_own_scope() {
    use heather_kernel::term::LocalVar;
    let psi = GlobalCtx::new(vec![]);
    let z = Level::Zero;
    let nat = || Rc::new(Type::Nat);
    let var = |i: u32| Rc::new(Term::Var(LocalVar(i)));
    // In (n): Σ(x:Nat). x = n.
    let record = Type::Sigma {
        fst_level: z.clone(), snd_level: z.clone(), fst: nat(),
        snd: Rc::new(Type::Id { level: z.clone(), ty: nat(), lhs: var(0), rhs: var(1) }),
    };
    for extra in [0u32, 1, 3] {
        // n, p, then `extra` more entries: p is `Var(extra)`, n `Var(extra + 1)`.
        let mut gamma = LocalCtx::nil().extended(nat(), z.clone()).extended(Rc::new(record.clone()), z.clone());
        for _ in 0..extra {
            gamma = gamma.extended(nat(), z.clone());
        }
        let p = var(extra);
        let proof = Term::SndAt { pair: Rc::clone(&p) };
        let first = Rc::new(Term::FstAt { pair: p });
        let claim = |rhs: Rc<Term>| Type::Id { level: z.clone(), ty: nat(), lhs: Rc::clone(&first), rhs };
        let seed = u64::from(extra);
        for layer in [Layer::Prog, Layer::Meta] {
            let expected = claim(var(extra + 1));
            assert_eq!(check_term(&psi, 0, layer, &gamma, &proof, &expected, &z, FUEL), Ok(()));
            check_tm(seed, "a projected variable", &psi, 0, layer, &gamma, &proof, &expected, &z, FUEL);
            infer_tm(seed, "a projected variable", &psi, 0, layer, &gamma, &proof, FUEL);
            // One entry inward of `n` is `p` itself, at the wrong type; with
            // entries after `p`, the one before it is a `Nat` that is not `n`.
            for wrong in [extra, extra.saturating_sub(1)] {
                let wrong = claim(var(wrong));
                assert!(check_term(&psi, 0, layer, &gamma, &proof, &wrong, &z, FUEL).is_err());
                check_tm(seed, "a projected variable at a neighbour", &psi, 0, layer, &gamma, &proof, &wrong, &z, FUEL);
            }
        }
    }
}

/// `app@` spines over a head whose Π needs reduction
/// (`docs/app-by-head-type-design.md` §3.2): a two-argument function stored
/// as a record field, `fst@(pair@^{T}(λx. λy. x; 0))` with
/// `T = El ⌜Σ(g : El ⌜Π(x:Nat). Π(y:Nat). Nat⌝). Nat⌝`, applied twice — the
/// second node's head type is the *first node's description*, so the chain
/// `Sel{Sel{Fst…}, App(a₁)}` forms, and each argument is checked at a domain
/// only evaluating that chain reveals. The generator's arm 32 reaches one
/// link; this is the length-two chain, with the negative control at each
/// argument position.
#[test]
fn app_at_spines_over_record_fields() {
    let psi = GlobalCtx::new(vec![]);
    let gamma = LocalCtx::nil();
    let z = Level::Zero;
    let pi2 = Term::TmPi {
        dom_level: z.clone(),
        cod_level: z.clone(),
        dom: Rc::new(enc_nat()),
        cod: Rc::new(Term::TmPi {
            dom_level: z.clone(),
            cod_level: z.clone(),
            dom: Rc::new(enc_nat()),
            cod: Rc::new(enc_nat()),
        }),
    };
    let rec_ty = el(enc_sigma(pi2, enc_nat()), z.clone());
    let nat_ty = Rc::new(Type::Nat);
    let k = Term::Lam {
        dom_level: z.clone(),
        cod_level: z.clone(),
        dom: Rc::clone(&nat_ty),
        body: Rc::new(Term::Lam {
            dom_level: z.clone(),
            cod_level: z.clone(),
            dom: Rc::clone(&nat_ty),
            body: Rc::new(Term::Var(heather_kernel::term::LocalVar(1))),
        }),
    };
    let head = Rc::new(Term::FstAt {
        pair: Rc::new(Term::PairAt {
            ty: Some(Rc::new(rec_ty)),
            fst: Rc::new(k),
            snd: Rc::new(Term::Zero),
        }),
    });
    let one = Rc::new(Term::Succ(Rc::new(Term::Zero)));
    let triv = Rc::new(Term::Triv { level: z.clone() });
    let app = |f: Rc<Term>, a: Rc<Term>| Rc::new(Term::AppAt { fun: f, arg: a });
    let partial = app(Rc::clone(&head), Rc::clone(&one));
    let full = app(Rc::clone(&partial), Rc::new(Term::Zero));
    let bad_first = app(app(Rc::clone(&head), Rc::clone(&triv)), Rc::new(Term::Zero));
    let bad_second = app(Rc::clone(&partial), Rc::clone(&triv));

    let before = heather_kernel::stats::snapshot();
    for layer in [Layer::Prog, Layer::Meta] {
        assert_eq!(
            check_term(&psi, 0, layer, &gamma, &full, &Type::Nat, &z, FUEL),
            Ok(()),
            "the spine must check at {layer:?}",
        );
        for (seed, (what, t)) in [
            ("one node", &partial),
            ("two nodes", &full),
            ("ill-typed first argument", &bad_first),
            ("ill-typed second argument", &bad_second),
        ]
        .into_iter()
        .enumerate()
        {
            let seed = seed as u64;
            infer_tm(seed, what, &psi, 0, layer, &gamma, t, FUEL);
            check_tm(seed, what, &psi, 0, layer, &gamma, t, &Type::Nat, &z, FUEL);
        }
        assert!(check_term(&psi, 0, layer, &gamma, &bad_first, &Type::Nat, &z, FUEL).is_err());
        assert!(check_term(&psi, 0, layer, &gamma, &bad_second, &Type::Nat, &z, FUEL).is_err());
    }
    let met = heather_kernel::stats::snapshot().since(&before);
    assert!(met.sel_evals > 0, "no Sel::App was evaluated — the stream is vacuous");
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
        ty: Some(Rc::new(ty.clone())),
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
