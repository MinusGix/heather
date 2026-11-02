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
//! - `level/equiv-shared` — the two sides are the *same* value. Constant
//!   time is a claim (`Rc` pointer equality decides a shared join at the
//!   root), and the flat slope is what states it.
//! - `level/equiv-rebuilt` — the two sides are equal but built separately,
//!   in opposite join orders, so they share no `Rc` and the comparison walks
//!   both joins' component slices. Linear, and it was linear with a
//!   `BTreeMap` per side before; what it guards is a comparison that grew
//!   past that.
//! - `level/join` — building `a ⊔ b` from two `n/2`-variable joins: the
//!   merge that canonicity costs, paid at construction. Expected ~n log n.

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

/// A level against itself — the case the conversion path actually meets most
/// often, where both sides came from the same annotation. Expected exponent
/// ~0: reflexivity is decided at the root.
fn equiv_shared() -> Family {
    let cases = [4u64, 8, 16, 32, 64]
        .iter()
        .map(|&n| {
            let a = tower(n as u32, true);
            let b = a.clone();
            let go = move || a.equiv(&b) as u64;
            assert!(go() == 1, "a level is not equivalent to itself at n = {n}");
            Case::new(n, 1, go)
        })
        .collect();
    Family {
        name: "level/equiv-shared",
        what: "l ≈ l on shared syntax — the reflexivity pre-check",
        unit: "variables",
        expect_slope: Some((-0.35, 0.45)),
        cases,
    }
}

/// Equal levels that share nothing: the same joins in the other order,
/// which canonicity makes the same value but not the same allocation.
fn equiv_rebuilt() -> Family {
    let cases = [4u64, 8, 16, 32, 64]
        .iter()
        .map(|&n| {
            let a = tower(n as u32, true);
            let b = tower(n as u32, false);
            assert!(a == b, "levels are canonical: the two towers must be one value");
            let go = move || a.equiv(&b) as u64;
            assert!(go() == 1, "the reordered join is not equivalent at n = {n}");
            Case::new(n, 1, go)
        })
        .collect();
    Family {
        name: "level/equiv-rebuilt",
        what: "l ≈ l' on equal levels built apart — the slice comparison",
        unit: "variables",
        expect_slope: Some((0.6, 1.5)),
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
            let go = move || matches!(Level::max(a.clone(), b.clone()), Level::Join(_)) as u64;
            assert!(go() == 1, "the join of disjoint towers is a join at n = {n}");
            Case::new(n, 1, go)
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
