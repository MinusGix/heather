//! Route 1 — the family by large elimination on the index
//! (`docs/inductives/inductive-indexed-lowering.md`), whose cost seam is §10.3: the whole
//! `elim_Nat`/`Case`/`elim_Wf` that *is* the family is inlined at every type
//! occurrence, and an indexed type appears inside other types.
//!
//! Route 1 had no swept family here until 2026-08-06, which is why its
//! §10.3 entry carried the phrase "[[frontend-benchmarks]] is where
//! 'acceptable' gets a number" for two rounds without one. The forded families
//! next door measure route 2b's `μ` and its skeleton type; neither multiplier
//! exists here, and route 2b's numbers moved twice without saying anything
//! about this scheme.
//!
//! One sweep, along the axis that multiplies both factors: the family's own
//! constructor count is the number of class members whose codes the family
//! node carries (Θ(n) nodes) *and* the number of `match` arms, each of which
//! re-emits the family at its branch index (Θ(n) occurrences).

use crate::harness::Family;
use heather_elab::IndexedRoute;

use super::scale::indexed_sweep;

pub fn families() -> Vec<Family> {
    vec![arms()]
}

/// A route-1 family with `n` constructors — `n − 1` of them in the successor
/// class — and the `n`-arm `match` over it.
fn arms() -> Family {
    let src = |n: u64| {
        let mut ctors = vec!["    C0                                 : Vf(0),".to_string()];
        let mut arms = vec!["        C0 => 0,".to_string()];
        for i in 1..n {
            // A *pattern* result index — `Vf(Succ(n))` with `n` a field — is
            // what makes this route 1 rather than fording (§3.2). All `n − 1`
            // land in the same class, so the successor branch's code is a Sum
            // of `n − 1` tag spines and the arm walk is a case tree over it.
            ctors.push(format!(
                "    C{i}(n: Nat, x{i}: Nat, t: Vf(n))    : Vf(Succ(n)),"
            ));
            arms.push(format!("        C{i}(m, y, u) => Succ(vsize(m, u)),"));
        }
        format!(
            "inductive Vf : (n: Nat) -> Type {{\n{}\n}}\n\
             fn vsize(n: Nat, t: Vf(n)) -> Nat {{\n    match t {{\n{}\n    }}\n}}\n",
            ctors.join("\n"),
            arms.join("\n"),
        )
    };
    Family {
        name: "indexed/arms",
        what: "a route-1 indexed family with n constructors, and the n-arm match over it",
        unit: "arms",
        // Recorded, not claimed. First measured 2026-08-06 by
        // `issues/family-types-as-code-defs.md` phase 5, against its own
        // registration-only build as the no-op point (design §8 phase 1's
        // discipline): **2.20 → 2.25**, with 249 µs → 216 µs at 2 arms and
        // 2.83 ms → 2.57 ms at 6. The constant moved ~1.10×; the exponent did
        // not move at all, and the reason is the same shape as the forded
        // suite's residual — what is still Θ(n) per arm is the **class**
        // type, the tag spine of the n−1 members sharing the successor
        // branch, which `indexed_class_body` whnfs the reference back into
        // and `spine` then re-emits into every injection annotation. No
        // registered code names a class; `D#fam` names the whole family.
        // Band records the exponent that exists, per the suite's rule; what
        // it guards is a third power appearing.
        //
        // 2026-08-17, re-recorded: **1.89** (six runs, range 1.86-1.93). The
        // old floor was 1.90 -- inside this family's own run-to-run range, so
        // the gate flipped red or green on which run you took. A boundary that
        // close to the measurement is not a claim about the cost model.
        expect_slope: Some((1.55, 2.25)),
        cases: indexed_sweep(
            "indexed/arms", &[2, 3, 4, 5, 6], "Vf", IndexedRoute::One, src,
        ),
    }
}
