//! **Differential test: conversion against conversion**
//! (docs/nbe-conversion-design.md §13 stage 2b, and that stage's kill
//! criterion).
//!
//! `tests/eval_differential.rs` holds the value machine's *weak head normal
//! forms* against the rewriter's. This file holds the thing the trusted base
//! actually publishes against itself: the **verdict**. `conv_term` decides
//! ch. 06's convertibility over values; `oracle::conv_term` decides it over
//! `reduce.rs`, which is ch. 06 transcribed rule for rule. Over the same
//! well-typed streams, on the same pairs, under the same budget, the two must
//! reach the same answer.
//!
//! ## The one asymmetry that is allowed
//!
//! Fuel. Sharing changes *how much* budget is enough — a value forced once
//! and reused costs the machine less than re-reducing costs the rewriter —
//! so the two accountings are not equal and were never going to be. What must
//! hold is the property fuel exists for (design §6):
//!
//! > an insufficient budget dies `OutOfFuel`; it never flips a verdict.
//!
//! So [`agree`] treats `OutOfFuel` from either side as "no answer offered"
//! and only ever compares two *verdicts*. The budget sweep in
//! [`fuel_never_flips_a_verdict`] is what makes that non-vacuous: it runs the
//! same pair at budgets from nothing to plenty and checks that every answer
//! either side gives agrees with the answer the other gives at full budget.
//!
//! ## δ, both ways
//!
//! Every stream runs twice: once over the generated Ψ, and once over
//! [`opaque`]'s copy of it with the definition bodies stripped. That is what
//! δ-opacity *is* for conversion — `Defs` is gated on Ψ holding a body — and
//! it exercises the δ-lazy stage's two exits (spine agreement without
//! unfolding, and unfolding after a failed spine).
//!
//! Failures report **seeds only**, per `CLAUDE.md`: a disagreeing pair is
//! exactly the term that OOMs a machine if Debug-formatted.

mod common;

use std::sync::Arc as Rc;

use common::wt::{
    gen_wt_ctx, gen_wt_env_at as gen_wt_env, gen_wt_term, gen_wt_term_at, gen_wt_type,
    identity_branches, identity_motives, perturb_conv, FUEL,
};
use common::Rng;
use heather_kernel::conv::{
    conv_local_ctx, conv_term, conv_type, oracle, ConvError,
};
use heather_kernel::layer::Layer;
use heather_kernel::level::Level;
use heather_kernel::term::{
    CtxBase, CtxEntry, GlobalBinding, GlobalCtx, GlobalVar, LocalCtx, LocalSubst, LocalVar,
    SubstTail, Term, Type,
};

/// Cases per seed stream. Six streams, each with its own mixer, for the
/// reason `ch05_06_lemmas.rs` records: the schedule finds defects the count
/// does not.
const CASES: u64 = 400;

/// Generator budget — how deep a well-typed term `wt.rs` synthesizes.
const BUDGET: u32 = 8;

type R = Result<(), ConvError>;

/// The two verdicts must agree. Exhaustion on either side is not a verdict
/// and is not a disagreement (see the module docs).
#[track_caller]
fn agree(seed: u64, what: &str, values: R, rewriter: R) {
    if values == Err(ConvError::OutOfFuel) || rewriter == Err(ConvError::OutOfFuel) {
        return;
    }
    assert!(
        values == rewriter,
        "seed {seed}: {what}: CONVERSION DISAGREEMENT — values said {}, the rewriter said {} \
         (terms suppressed on purpose)",
        verdict(values),
        verdict(rewriter),
    );
}

fn verdict(r: R) -> &'static str {
    match r {
        Ok(()) => "convertible",
        Err(ConvError::NotConvertible) => "not convertible",
        Err(ConvError::OutOfFuel) => "out of fuel",
    }
}

#[test]
fn maximum_nat_literals_compare_by_run_fragments() {
    let psi = GlobalCtx::new(vec![]);
    let gamma = LocalCtx::nil();
    let maximum = Term::NatLit(u64::MAX.into());
    assert_eq!(
        conv_term(
            &psi,
            &gamma,
            Layer::Prog,
            &maximum,
            &maximum,
            &Type::Nat,
            &Level::Zero,
            8,
        ),
        Ok(()),
    );
    assert_eq!(
        conv_term(
            &psi,
            &gamma,
            Layer::Prog,
            &maximum,
            &Term::NatLit((u64::MAX - 1).into()),
            &Type::Nat,
            &Level::Zero,
            8,
        ),
        Err(ConvError::NotConvertible),
    );
}

/// Both engines on the same term pair.
#[allow(clippy::too_many_arguments)]
fn both_tm(
    psi: &GlobalCtx,
    gamma: &LocalCtx,
    layer: Layer,
    a: &Term,
    b: &Term,
    ty: &Type,
    l: &Level,
    fuel: u64,
) -> (R, R) {
    (
        conv_term(psi, gamma, layer, a, b, ty, l, fuel),
        oracle::conv_term(psi, gamma, layer, a, b, ty, l, fuel),
    )
}

fn both_ty(
    psi: &GlobalCtx,
    gamma: &LocalCtx,
    layer: Layer,
    a: &Type,
    b: &Type,
    l: &Level,
    fuel: u64,
) -> (R, R) {
    (
        conv_type(psi, gamma, layer, a, b, l, fuel),
        oracle::conv_type(psi, gamma, layer, a, b, l, fuel),
    )
}

/// A term pair, checked in both δ modes: the ambient Ψ, and the same Ψ with
/// every definition body removed.
#[allow(clippy::too_many_arguments)]
fn check_tm(
    seed: u64,
    what: &str,
    psi: &GlobalCtx,
    gamma: &LocalCtx,
    layer: Layer,
    a: &Term,
    b: &Term,
    ty: &Type,
    l: &Level,
) {
    let (x, y) = both_tm(psi, gamma, layer, a, b, ty, l, FUEL);
    agree(seed, what, x, y);
    let dark = opaque(psi);
    let (x, y) = both_tm(&dark, gamma, layer, a, b, ty, l, FUEL);
    agree(seed, &format!("{what} [δ-opaque]"), x, y);
}

fn check_ty(
    seed: u64,
    what: &str,
    psi: &GlobalCtx,
    gamma: &LocalCtx,
    layer: Layer,
    a: &Type,
    b: &Type,
    l: &Level,
) {
    let (x, y) = both_ty(psi, gamma, layer, a, b, l, FUEL);
    agree(seed, what, x, y);
    let dark = opaque(psi);
    let (x, y) = both_ty(&dark, gamma, layer, a, b, l, FUEL);
    agree(seed, &format!("{what} [δ-opaque]"), x, y);
}

/// The same Ψ with its definitions turned back into declarations — which is
/// exactly what `Defs::opaque` makes of it.
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

// ---------------------------------------------------------------------------
// Stream 1: generated triples — reflexivity, and a negative control
// ---------------------------------------------------------------------------

#[test]
fn stream1_generated_terms_and_types() {
    for seed in 0..CASES {
        let mut r = Rng::new(seed ^ 0x9e3779b97f4a7c15);
        let env = gen_wt_env(&mut r);
        let (t, ty, l) = gen_wt_term(&env, &mut r, BUDGET);
        check_tm(seed, "t ≈ t", &env.psi, &env.gamma, env.layer, &t, &t, &ty, &l);
        check_ty(seed, "T ≈ T", &env.psi, &env.gamma, env.layer, &ty, &ty, &l);

        // Negative control: a second generated term at the same type is
        // usually *not* convertible, and whatever it is, both engines must
        // say the same thing (docs/testing-generated-terms.md axis 4).
        if let Some(u) = gen_wt_term_at(&env, &mut r, BUDGET, &ty, &l) {
            check_tm(seed, "t ≈ u", &env.psi, &env.gamma, env.layer, &t, &u, &ty, &l);
        }
    }
}

// ---------------------------------------------------------------------------
// Stream 2: perturbed twins — pairs that are convertible only after reducing
// ---------------------------------------------------------------------------

#[test]
fn stream2_perturbed_twins() {
    for seed in 0..CASES {
        let mut r = Rng::new(seed ^ 0x517cc1b727220a95);
        let env = gen_wt_env(&mut r);
        let (t, ty, l) = gen_wt_term(&env, &mut r, BUDGET);
        let Some(p) = perturb_conv(&env, &mut r, &t, &ty, &l) else {
            panic!("seed {seed}: no perturbation applicable");
        };
        check_tm(seed, "t ≈ perturb(t)", &env.psi, &env.gamma, env.layer, &t, &p, &ty, &l);
        // Both directions: the algorithm is left-biased, so a disagreement
        // can hide on one side only.
        check_tm(seed, "perturb(t) ≈ t", &env.psi, &env.gamma, env.layer, &p, &t, &ty, &l);
    }
}

// ---------------------------------------------------------------------------
// Stream 3: open terms in a non-empty Γ at a *checked* type
// ---------------------------------------------------------------------------

#[test]
fn stream3_open_terms_and_contexts() {
    for seed in 0..CASES {
        let mut r = Rng::new(seed ^ 0x2545f4914f6cdd1d);
        let mut env = gen_wt_env(&mut r);
        env.gamma = gen_wt_ctx(&env, &mut r, 4, env.layer);
        if env.gamma.entries.is_empty() {
            env.gamma.entries.push(CtxEntry { ty: Rc::new(Type::Nat), level: Level::Zero });
        }
        let (ty, l) = gen_wt_type(&env, &mut r, BUDGET / 2);
        let Some(t) = gen_wt_term_at(&env, &mut r, BUDGET, &ty, &l) else { continue };
        check_tm(seed, "open t ≈ t", &env.psi, &env.gamma, env.layer, &t, &t, &ty, &l);
        check_ty(seed, "open T ≈ T", &env.psi, &env.gamma, env.layer, &ty, &ty, &l);

        // Each Γ entry type in its own prefix — the scopes the value domain's
        // two-part variable identity is about.
        for k in 0..env.gamma.entries.len() {
            let prefix =
                env.gamma.prefix(k);
            let ety = Rc::clone(&env.gamma.entries[k].ty);
            let lvl = env.gamma.entries[k].level.clone();
            check_ty(seed, "Γ entry", &env.psi, &prefix, env.layer, &ety, &ety, &lvl);
        }

        // The context judgment itself.
        agree(
            seed,
            "Γ ≈ Γ",
            conv_local_ctx(&env.psi, env.layer, &env.gamma, &env.gamma, FUEL),
            oracle::conv_local_ctx(&env.psi, env.layer, &env.gamma, &env.gamma, FUEL),
        );
    }
}

// ---------------------------------------------------------------------------
// Stream 4: the code recursors, plain and under a β-redex
// ---------------------------------------------------------------------------

/// `(λ(_ : Nat). t↑) ze` — by the time `t` is reached the environment is one
/// longer than the Γ its reduct lives in, which is where the shared β
/// helpers' materialized `id_Γ` and the value's own scope stop coinciding.
fn under_beta(t: Rc<Term>, ty: &Type, level: &Level) -> Rc<Term> {
    Rc::new(Term::App {
        fun: Rc::new(Term::Lam {
            dom_level: Level::Zero,
            cod_level: level.clone(),
            dom: Rc::new(Type::Nat),
            body: Rc::new(t.shift_local(1)),
        }),
        dom_level: Level::Zero,
        cod_level: level.clone(),
        dom: Rc::new(Type::Nat),
        cod: Rc::new(ty.shift_local(1)),
        arg: Rc::new(Term::Zero),
    })
}

#[test]
fn stream4_code_recursors() {
    for seed in 0..CASES {
        let mut r = Rng::new(seed ^ 0xc3a5c85c97cb3127);
        let mut env = gen_wt_env(&mut r);
        env.layer = Layer::Meta;
        let delta = gen_wt_ctx(&env, &mut r, 4, Layer::Prog);
        let ce = env.in_ctx(delta.clone(), Layer::Code);

        let (code, cl) = gen_wt_type(&ce, &mut r, BUDGET);
        let ty = Type::CodeTy { ctx: delta.clone(), level: cl.clone() };
        let t = Rc::new(Term::ElimCodeTy {
            ty_motive_level: Level::Zero,
            tm_motive_level: Level::Zero,
            motives: identity_motives(),
            branches: identity_branches(),
            code_level: cl,
            ctx: delta.clone(),
            scrut: Rc::new(Term::BoxTy(code)),
        });
        check_tm(
            seed,
            "identity elim^Typ",
            &env.psi,
            &env.gamma,
            env.layer,
            &t,
            &t,
            &ty,
            &Level::Zero,
        );
        let w = under_beta(Rc::clone(&t), &ty, &Level::Zero);
        // The recursor against its own β-wrapped twin: the two sides reach
        // the same value through different scopes.
        check_tm(
            seed,
            "elim^Typ ≈ (λ_. elim^Typ) ze",
            &env.psi,
            &env.gamma,
            env.layer,
            &t,
            &w,
            &ty,
            &Level::Zero,
        );

        let (code, cty, cl) = gen_wt_term(&ce, &mut r, BUDGET);
        let ty = Type::CodeTm { ctx: delta.clone(), ty: Rc::clone(&cty), level: cl.clone() };
        let t = Rc::new(Term::ElimCodeTm {
            ty_motive_level: Level::Zero,
            tm_motive_level: Level::Zero,
            motives: identity_motives(),
            branches: identity_branches(),
            code_level: cl,
            ctx: delta,
            ty: cty,
            scrut: Rc::new(Term::BoxTm(code)),
        });
        check_tm(
            seed,
            "identity elim^Trm",
            &env.psi,
            &env.gamma,
            env.layer,
            &t,
            &t,
            &ty,
            &Level::Zero,
        );
        let w = under_beta(Rc::clone(&t), &ty, &Level::Zero);
        check_tm(
            seed,
            "elim^Trm ≈ (λ_. elim^Trm) ze",
            &env.psi,
            &env.gamma,
            env.layer,
            &t,
            &w,
            &ty,
            &Level::Zero,
        );
    }
}

// ---------------------------------------------------------------------------
// Stream 5: definitions — the δ-lazy stage, both of its exits
// ---------------------------------------------------------------------------

fn defs_psi(body: Rc<Term>) -> (GlobalCtx, LocalCtx) {
    let delta = LocalCtx {
        base: CtxBase::Nil,
        entries: (vec![CtxEntry { ty: Rc::new(Type::Nat), level: Level::Zero }]).into(),
    };
    let psi = GlobalCtx::new(vec![GlobalBinding::defined_tm(
        delta.clone(),
        Layer::Code,
        Rc::new(Type::Nat),
        Level::Zero,
        body,
    )]);
    (psi, delta)
}

fn nat_rec(scrut: Rc<Term>) -> Rc<Term> {
    Rc::new(Term::ElimNat {
        level: Level::Zero,
        motive: Rc::new(Type::Nat),
        base: Rc::new(Term::Zero),
        step: Rc::new(Term::Succ(Rc::new(Term::Var(LocalVar(0))))),
        scrut,
    })
}

fn numeral(n: u32) -> Rc<Term> {
    let mut t = Rc::new(Term::Zero);
    for _ in 0..n {
        t = Rc::new(Term::Succ(t));
    }
    t
}

fn global_at(payload: Rc<Term>) -> Rc<Term> {
    Rc::new(Term::GlobalTm {
        var: GlobalVar(0),
        subst: LocalSubst {
            tail: SubstTail::Empty { len: 1, base: CtxBase::Nil },
            terms: vec![payload],
        },
    })
}

#[test]
fn stream5_definitions_and_delta() {
    for seed in 0..CASES {
        let mut r = Rng::new(seed ^ 0xff51afd7ed558ccd);
        let delta = LocalCtx {
            base: CtxBase::Nil,
            entries: (vec![CtxEntry { ty: Rc::new(Type::Nat), level: Level::Zero }]).into(),
        };
        let base_env = gen_wt_env(&mut r);
        let benv = base_env.in_ctx(delta.clone(), Layer::Prog);
        let body = gen_wt_term_at(&benv, &mut r, BUDGET, &Type::Nat, &Level::Zero)
            .unwrap_or_else(|| Rc::new(Term::Var(LocalVar(0))));
        let (psi, _) = defs_psi(body);
        let gamma = LocalCtx {
            base: CtxBase::Nil,
            entries: (vec![CtxEntry { ty: Rc::new(Type::Nat), level: Level::Zero }]).into(),
        };
        let payloads = [
            numeral((seed % 4) as u32),
            nat_rec(numeral((seed % 3) as u32)),
            nat_rec(Rc::new(Term::Var(LocalVar(0)))),
            nat_rec(nat_rec(numeral((seed % 3) as u32))),
        ];
        for (i, payload) in payloads.iter().enumerate() {
            let u = global_at(Rc::clone(payload));
            // Same head, same spine: the δ-lazy stage settles without ever
            // materializing the body.
            check_tm(
                seed,
                &format!("u^δ ≈ u^δ ({i})"),
                &psi,
                &gamma,
                Layer::Prog,
                &u,
                &u,
                &Type::Nat,
                &Level::Zero,
            );
            // Same head, *different* spine: the spine comparison fails and
            // both sides unfold.
            let v = global_at(Rc::new(Term::Succ(Rc::clone(payload))));
            check_tm(
                seed,
                &format!("u^δ ≈ u^(su δ) ({i})"),
                &psi,
                &gamma,
                Layer::Prog,
                &u,
                &v,
                &Type::Nat,
                &Level::Zero,
            );
            // A definition against something that is not one.
            let n = nat_rec(Rc::clone(&u));
            check_tm(
                seed,
                &format!("elim u^δ ≈ u^δ ({i})"),
                &psi,
                &gamma,
                Layer::Prog,
                &n,
                &u,
                &Type::Nat,
                &Level::Zero,
            );
        }
    }
}

// ---------------------------------------------------------------------------
// Fuel: a budget buys an answer or nothing, never a different answer
// ---------------------------------------------------------------------------

/// The property of design §6, stated as a property because sharing makes the
/// *threshold* a cost model: at every budget, each engine either reports
/// `OutOfFuel` or reaches the verdict the other reaches at full budget.
#[test]
fn fuel_never_flips_a_verdict() {
    for seed in 0..CASES {
        let mut r = Rng::new(seed ^ 0x8ebc6af09c88c6e3);
        let env = gen_wt_env(&mut r);
        let (t, ty, l) = gen_wt_term(&env, &mut r, BUDGET);
        let Some(p) = perturb_conv(&env, &mut r, &t, &ty, &l) else { continue };
        let (truth, oracle) =
            both_tm(&env.psi, &env.gamma, env.layer, &t, &p, &ty, &l, FUEL);
        agree(seed, "reference verdict", truth, oracle);
        if truth == Err(ConvError::OutOfFuel) {
            continue;
        }
        let mut answered = false;
        for budget in [0u64, 1, 2, 4, 8, 16, 64, 256, 1024] {
            let (x, y) = both_tm(&env.psi, &env.gamma, env.layer, &t, &p, &ty, &l, budget);
            for (engine, got) in [("values", x), ("rewriter", y)] {
                match got {
                    Err(ConvError::OutOfFuel) => {}
                    v => {
                        answered = true;
                        assert!(
                            v == truth,
                            "seed {seed}: budget {budget} flipped the {engine} verdict to {} \
                             (full budget says {})",
                            verdict(v),
                            verdict(truth),
                        );
                    }
                }
            }
        }
        assert!(answered, "seed {seed}: no budget in the sweep answered at all");
    }
}
