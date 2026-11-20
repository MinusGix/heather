//! The evaluator's run machinery (`eval/runs.rs`, `value/algebra.rs`): folds
//! over numbers it recognizes and does not walk. An affine fold (`add`,
//! `mul`'s inner `add`) moves its whole count in one step, a synchronous one
//! (`max`) cancels a shared prefix, and a run over an open tail keeps its
//! count beside the variable. The claim every family here checks is the one
//! the design rests on: **cost independent of the magnitude**. Sizes are
//! the numbers' bit widths, so the counters are flat; a walk one successor
//! at a time would be exponential in the size axis and would not finish.
//!
//! The *time* is not flat past one word: `issues/wide-literal-run-cost.md`
//! (a 60× step from 64 to 256 bits, then a slope of about 1.5 in the width,
//! in numeral arithmetic no counter sees). The bands record that exponent;
//! they become `(-0.25, 0.35)` when it is fixed.
//!
//! `run/fuel-exhaustion` is the other side: a fold the machinery cannot
//! accelerate, run into a fuel limit. Fuel bounds its steps and, since
//! `ARENA_BYTES_LIMIT`, the memory those steps take; the family pins steps
//! and arena bytes per unit of fuel.

use heather_kernel::conv::{conv_term, ConvError};
use heather_kernel::layer::Layer;
use heather_kernel::level::Level;
use heather_kernel::term::{CtxEntry, GlobalCtx, LocalCtx, Numeral, Term, Type};


use super::delta::{app2, app_at, lam, max_def, nat2_to_nat, nat_to_nat, Defs};
use super::terms::{add, mul, nil_ctx, rt, rty, v};
use super::FUEL;
use crate::harness::{Case, Family};

pub fn families() -> Vec<Family> {
    vec![affine_literal(), sync_literal(), mul_literal(), open_tail(), fuel_exhaustion()]
}

/// Bit widths: one limb, then several.
const BITS: [u64; 5] = [16, 64, 256, 1024, 4096];

/// `2^bits - 1`, every bit set.
fn ones(bits: u64) -> Numeral {
    let mut limbs = vec![u64::MAX; (bits / 64) as usize];
    if bits % 64 != 0 {
        limbs.push((1u64 << (bits % 64)) - 1);
    }
    Numeral::from_limbs(limbs)
}

fn lit(n: Numeral) -> Term {
    Term::NatLit(n)
}

/// `2^bits - 1 - k`, for small `k`.
fn ones_minus(bits: u64, k: u64) -> Numeral {
    let mut n = ones(bits);
    for _ in 0..k {
        n = n.pred().expect("ones() is large");
    }
    n
}

fn conv_nat(size: u64, psi: GlobalCtx, gamma: LocalCtx, lhs: Term, rhs: Term) -> Case {
    let go = move || {
        conv_term(&psi, &gamma, Layer::Prog, &lhs, &rhs, &Type::Nat, &Level::Zero, FUEL).is_ok() as u64
    };
    assert!(go() == 1, "the {size}-bit run fixture does not convert");
    Case::new(size, 1, go)
}

/// `add(N, 7) ≡ add(N - 3, 10)` for `N = 2^bits - 1`, with the recursion on
/// the first argument: two affine folds of `N` and `N - 3` steps, each one
/// step of the run machinery, compared as numbers.
fn affine_literal() -> Family {
    let cases = BITS
        .iter()
        .map(|&bits| {
            let lhs = add(lit(ones(bits)), lit(7u64.into()));
            let rhs = add(lit(ones_minus(bits, 3)), lit(10u64.into()));
            conv_nat(bits, GlobalCtx::default(), nil_ctx(), lhs, rhs)
        })
        .collect();
    Family {
        name: "run/affine-literal",
        what: "add(2ᵇ-1, 7) ≡ add(2ᵇ-4, 10) — affine folds of literal length",
        unit: "bits",
        expect_slope: Some((1.0, 2.0)),
        cases,
    }
}

/// `max(N, N - 5) ≡ N` through the defined synchronous `max`: the shared
/// prefix of `N - 5` successors cancels in one step.
fn sync_literal() -> Family {
    let cases = BITS
        .iter()
        .map(|&bits| {
            let mut ds = Defs::new();
            let max = ds.push(nat2_to_nat(), |_| max_def());
            let (psi, len) = ds.finish();
            let lhs = app2(Defs::at(max, len), lit(ones(bits)), lit(ones_minus(bits, 5)));
            conv_nat(bits, psi, nil_ctx(), lhs, lit(ones(bits)))
        })
        .collect();
    Family {
        name: "run/sync-literal",
        what: "max(2ᵇ-1, 2ᵇ-6) ≡ 2ᵇ-1 — a synchronous fold over literals",
        unit: "bits",
        expect_slope: Some((1.0, 2.0)),
        cases,
    }
}

/// `mul(N, 3) ≡ add(N, add(N, N))`: a fold whose step is itself an affine
/// fold (`add(3, ih)`), iterated `N` times.
fn mul_literal() -> Family {
    let cases = BITS
        .iter()
        .map(|&bits| {
            let n = || lit(ones(bits));
            let lhs = mul(n(), lit(3u64.into()));
            let rhs = add(n(), add(n(), n()));
            conv_nat(bits, GlobalCtx::default(), nil_ctx(), lhs, rhs)
        })
        .collect();
    Family {
        name: "run/mul-literal",
        what: "mul(2ᵇ-1, 3) ≡ add(2ᵇ-1, add(2ᵇ-1, 2ᵇ-1)) — an affine fold of affine steps",
        unit: "bits",
        expect_slope: Some((1.0, 2.0)),
        cases,
    }
}

/// `add(N, x) ≡ add(N - 1, Succ x)` under `x : Nat`: runs over an **open**
/// tail, where the count stays beside the variable instead of reaching
/// `Zero`.
fn open_tail() -> Family {
    let cases = BITS
        .iter()
        .map(|&bits| {
            let mut gamma = nil_ctx();
            gamma.entries.push(CtxEntry { ty: rty(Type::Nat), level: Level::Zero });
            let lhs = add(lit(ones(bits)), v(0));
            let rhs = add(lit(ones_minus(bits, 1)), Term::Succ(rt(v(0))));
            conv_nat(bits, GlobalCtx::default(), gamma, lhs, rhs)
        })
        .collect();
    Family {
        name: "run/open-tail",
        what: "add(2ᵇ-1, x) ≡ add(2ᵇ-2, Succ x) — affine runs over a variable",
        unit: "bits",
        expect_slope: Some((1.0, 2.0)),
        cases,
    }
}

/// `loop(2⁶⁴-1)(0) ≡ 1` at a fuel budget, for `loop(n) := elim_Nat(n;
/// Nat → Nat; λa. a; _ ih. λa. ih(a))`: a fold the machinery does not
/// accelerate, whose steps are tail calls, so the run is bounded by fuel and
/// not by depth (a fold that nests its hypothesis is refused at
/// `NATIVE_DEPTH_LIMIT` first, whatever the budget). The size is the budget:
/// steps grow linearly in it, and arena bytes must too, which is the
/// property `ARENA_BYTES_LIMIT` backs.
fn fuel_exhaustion() -> Family {
    let looped = |n: Term| {
        let fold = Term::ElimNat {
            level: Level::Zero,
            motive: rty(nat_to_nat()),
            base: rt(lam(v(0))),
            // Under the step's binders ih = 0, k = 1; under λa, a = 0, ih = 1.
            step: rt(lam(app_at(v(1), v(0), Type::Nat))),
            scrut: rt(n),
        };
        app_at(fold, Term::Zero, Type::Nat)
    };
    let cases = [1u64 << 12, 1 << 13, 1 << 14, 1 << 15, 1 << 16]
        .iter()
        .map(|&fuel| {
            let lhs = looped(lit(ones(64)));
            let rhs = Term::Succ(rt(Term::Zero));
            let gamma = nil_ctx();
            let psi = GlobalCtx::default();
            let go = move || conv_term(&psi, &gamma, Layer::Prog, &lhs, &rhs, &Type::Nat, &Level::Zero, fuel);
            assert_eq!(go(), Err(ConvError::OutOfFuel), "fuel {fuel}: the loop finished or mismatched");
            Case::new(fuel, 0, move || go().is_ok() as u64)
        })
        .collect();
    Family {
        name: "run/fuel-exhaustion",
        what: "a tail-calling fold of 2⁶⁴ steps refused at a budget — cost per unit of fuel",
        unit: "fuel",
        expect_slope: Some((0.80, 1.25)),
        cases,
    }
}
