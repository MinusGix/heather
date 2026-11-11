//! Universe-level equivalence. Levels are judgment-level data — inert to
//! reduction — but every conversion and every checking rule that mentions a
//! level compares one, so their cost is a *multiplier* on the rest of the
//! kernel rather than a line item: a real profile once put level arithmetic
//! at ~14% of a whole `heather check` run
//! ([[level-normalization-allocation]]).
//!
//! Levels are canonical by construction (`issues/kernel-compact-level.md`),
//! so `equiv` is `==` and the normalization a comparison used to run now
//! runs once, when a join is built. Three families:
//!
//! A level is one word (`issues/kernel-level-eight-bytes.md`): a join is
//! its index in the process's table, so a comparison reads no join at all.
//!
//! - `level/equiv-shared` — the two sides are the *same* value. Constant
//!   time is a claim, and the flat slope is what states it.
//! - `level/equiv-rebuilt` — the two sides are equal but built separately,
//!   in opposite join orders. One join has one word however it was built,
//!   so this is flat too; it was linear while a join was compared by its
//!   components, and what it guards is a comparison that reads them again.
//! - `level/join` — building `a ⊔ b` from two `n/2`-variable joins: the
//!   merge that canonicity costs and the table lookup that finds the word,
//!   paid at construction. Expected ~n log n.

use heather_kernel::level::{Level, UnivVar};

use crate::harness::{Case, Family};

pub fn families() -> Vec<Family> {
    vec![equiv_shared(), equiv_rebuilt(), join()]
}

/// `⨆_{i<n} (i mod 3) + ℓᵢ`, built left to right (`fwd`) or right to left.
/// `⊔` is associative and commutative, so the two are equivalent and — for
/// `n > 1` — not the same syntax.
fn tower(n: u32, fwd: bool) -> Level {
    let one = |i: u32| {
        let mut v = Level::Var(UnivVar(i));
        for _ in 0..(i % 3) {
            v = Level::succ(v);
        }
        v
    };
    let mut l = Level::Zero;
    for k in 0..n {
        l = Level::max(l, one(if fwd { k } else { n - 1 - k }));
    }
    l
}

/// Comparisons per timed call. One is a nanosecond, which is the timer's
/// noise and not the comparison's cost; a batch is something the gate's
/// ratio test can hold.
const BATCH: u64 = 64;

/// How many of [`BATCH`] comparisons of `a` with `b` say equivalent.
fn equivs(a: &Level, b: &Level) -> u64 {
    (0..BATCH).map(|_| std::hint::black_box(a).equiv(std::hint::black_box(b)) as u64).sum()
}

/// A level against itself — the case the conversion path actually meets most
/// often, where both sides came from the same annotation. Expected exponent
/// ~0: the two are one word.
fn equiv_shared() -> Family {
    let cases = [4u64, 8, 16, 32, 64]
        .iter()
        .map(|&n| {
            let a = tower(n as u32, true);
            let b = a.clone();
            let go = move || equivs(&a, &b);
            assert!(go() == BATCH, "a level is not equivalent to itself at n = {n}");
            Case::new(n, BATCH, go)
        })
        .collect();
    Family {
        name: "level/equiv-shared",
        what: "l ≈ l, 64 times — the same word",
        unit: "variables",
        expect_slope: Some((-0.35, 0.45)),
        cases,
    }
}

/// Equal levels built apart: the same joins in the other order, which
/// canonicity makes the same value and the table the same word.
fn equiv_rebuilt() -> Family {
    let cases = [4u64, 8, 16, 32, 64]
        .iter()
        .map(|&n| {
            let a = tower(n as u32, true);
            let b = tower(n as u32, false);
            assert!(a == b, "levels are canonical: the two towers must be one value");
            let go = move || equivs(&a, &b);
            assert!(go() == BATCH, "the reordered join is not equivalent at n = {n}");
            Case::new(n, BATCH, go)
        })
        .collect();
    Family {
        name: "level/equiv-rebuilt",
        what: "l ≈ l' on equal levels built apart, 64 times — one join, one word",
        unit: "variables",
        expect_slope: Some((-0.35, 0.45)),
        cases,
    }
}

/// `a ⊔ b` for two disjoint `n/2`-variable joins, the merge canonicity pays
/// at construction instead of at every comparison.
fn join() -> Family {
    let cases = [4u64, 8, 16, 32, 64]
        .iter()
        .map(|&n| {
            let half = (n / 2) as u32;
            let a = tower(half, true);
            let b = tower(half, true).shift(half, 0);
            let go = move || Level::max(a.clone(), b.clone()).parts().map_or(0, |(_, vars)| vars.len() as u64);
            assert!(go() == n, "the join of disjoint towers has every variable at n = {n}");
            Case::new(n, n, go)
        })
        .collect();
    Family {
        name: "level/join",
        what: "a ⊔ b of two n/2-variable joins — the canonicalizing merge",
        unit: "variables",
        expect_slope: Some((0.2, 1.4)),
        cases,
    }
}
