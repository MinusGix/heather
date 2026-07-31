//! Universe-level equivalence. Levels are judgment-level data — inert to
//! reduction — but every conversion and every checking rule that mentions a
//! level compares one, so their cost is a *multiplier* on the rest of the
//! kernel rather than a line item: a real profile once put level arithmetic
//! at ~14% of a whole `heather check` run
//! ([[level-normalization-allocation]]).
//!
//! Two families, because level comparison has two regimes and they must not
//! be conflated:
//!
//! - `level/equiv-shared` — the two sides are the *same* syntax. Constant
//!   time is a claim (`Level::equiv`'s reflexivity pre-check, with `Rc`
//!   pointer equality stopping the walk at shared subtrees), and the flat
//!   slope is what states it.
//! - `level/equiv-rebuilt` — the two sides are equivalent but structurally
//!   distinct, so the pre-check *misses* and the full `adjust(count(l))`
//!   normalization runs on both. This is the family that guards against a
//!   fast path that quietly became the only path.

use heather_kernel::level::{Level, UnivVar};

use crate::harness::{Case, Family};

pub fn families() -> Vec<Family> {
    vec![equiv_shared(), equiv_rebuilt()]
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

/// Equivalent levels the pre-check cannot see: the same joins in the other
/// order. Both sides normalize in full.
fn equiv_rebuilt() -> Family {
    let cases = [4u64, 8, 16, 32, 64]
        .iter()
        .map(|&n| {
            let a = tower(n as u32, true);
            let b = tower(n as u32, false);
            assert!(n < 2 || a != b, "the two towers must not be the same syntax");
            let go = move || a.equiv(&b) as u64;
            assert!(go() == 1, "the reordered join is not equivalent at n = {n}");
            Case::new(n, 1, go)
        })
        .collect();
    Family {
        name: "level/equiv-rebuilt",
        what: "l ≈ l' on equivalent-but-distinct syntax — the normalize path",
        unit: "variables",
        expect_slope: Some((0.85, 1.65)),
        cases,
    }
}
