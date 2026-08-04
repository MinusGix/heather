//! **The round's soul** — the forded families, whose cost is what a kernel
//! `def` for generated terms is meant to cut
//! (`docs/inductive-fording-lowering.md` §14.2 and §14.9, and the two
//! 2026-08-04 trigger entries in `issues/frontend-benchmarks.md`).
//!
//! The seam, in one paragraph. A forded declaration lowers to
//! `Σ(s : Skel). sEq(I; μ s; m)`, and `μ` — the index measure — is a whole
//! `elim_Wf` **inlined at every occurrence**, because the kernel term
//! language has no definitions (`issues/simulate-conversion-cost.md`). The
//! family type contains one; the eliminator instantiates it several times per
//! arm; a forded type appearing inside another type multiplies that again;
//! and at a *declared* index (form A) each arm additionally emits one
//! `child_projection` per child and one tag predicate per other index
//! constructor, each itself a whole `elim_Wf`. Three sweeps, one per
//! multiplier:
//!
//! | family | swept axis | seam |
//! |---|---|---|
//! | `forded/computed-arms` | constructors of the forded family = match arms | §14.2 |
//! | `forded/occurrences` | uses of one forded family in other declarations | §14.2 |
//! | `forded/declared-index-tags` | constructors of the *index* type | §14.9 |
//!
//! **The bands below record the exponents that exist today, not the ones the
//! design wants**, which is the kernel doc's rule for a band that records a
//! defect (docs/benchmarking.md, "Adding a family"). Two of the three are
//! superlinear; a linear-in-arms elaborator is the outcome that would make
//! them fail low, and when the kernel-def round lands that is exactly what
//! should happen — the right response then is `--save` and a note that the
//! before/after is these three families. Phase 2's "before" is here.

use crate::harness::Family;

use super::scale::sweep;

const ADD: &str = "fn add(a: Nat, b: Nat) -> Nat { match b { Zero => a, Succ(k) => Succ(add(a, k)) } }\n";

pub fn families() -> Vec<Family> {
    vec![computed_arms(), occurrences(), declared_index_tags()]
}

/// A route-2b family with `n` constructors — computed result indices,
/// recursive children — and the `n`-arm `match` over it. Every arm carries
/// its own copy of the fording machinery, so this is §14.2's multiplier at
/// its most direct.
fn computed_arms() -> Family {
    let src = |n: u64| {
        let mut ctors = vec!["    C0                                    : F(0),".to_string()];
        let mut arms = vec!["        C0 => 0,".to_string()];
        for i in 1..n {
            // A variable child index, a payload that does not depend on it,
            // and a computed result index: route 2b, not route 1 (§3.2).
            ctors.push(format!(
                "    C{i}(n: Nat, x: Nat, t: F(n))          : F(Succ(add(n, {i}))),"
            ));
            arms.push(format!("        C{i}(m, y, u) => Succ(fsize(m, u)),"));
        }
        format!(
            "{ADD}inductive F : (n: Nat) -> Type {{\n{}\n}}\n\
             fn fsize(n: Nat, t: F(n)) -> Nat {{\n    match t {{\n{}\n    }}\n}}\n",
            ctors.join("\n"),
            arms.join("\n"),
        )
    };
    Family {
        name: "forded/computed-arms",
        what: "a route-2b family with n constructors, and the n-arm match over it",
        unit: "arms",
        // ~3.3 measured 2026-08-04 (25 ms → 1.0 s from 2 to 6 arms). Cubic
        // in the arm count for a file whose *source* grows linearly: μ is
        // inlined per arm, the eliminator instantiates it per arm, and the
        // kernel re-checks the product. The band is this defect's record.
        // §14.2's fix (a kernel `def`) should drop it towards 1–2.
        expect_slope: Some((2.60, 4.00)),
        cases: sweep("forded/computed-arms", &[2, 3, 4, 5, 6], src),
    }
}

/// One fixed 3-constructor forded family, used by `n` separate declarations.
/// §14.2's other clause — "a forded type appearing in another type
/// multiplies that" — as a straight repetition, so the *slope* should be 1
/// and the number that matters is the **per-occurrence cost**: what a user
/// pays for each place a forded family is mentioned. That per-unit figure is
/// the one the kernel-def round should move, and it is printed per case.
fn occurrences() -> Family {
    let fam = format!(
        "{ADD}inductive F : (n: Nat) -> Type {{\n\
         \x20   C0                                    : F(0),\n\
         \x20   C1(n: Nat, x: Nat, t: F(n))           : F(Succ(add(n, 1))),\n\
         \x20   C2(n: Nat, x: Nat, t: F(n))           : F(Succ(add(n, 2))),\n\
         }}\n"
    );
    let src = move |n: u64| {
        let mut s = fam.clone();
        for i in 0..n {
            s.push_str(&format!(
                "fn use{i}(n: Nat, t: F(n)) -> Nat {{\n    \
                 match t {{ C0 => {i}, C1(m, y, u) => Succ(use{i}(m, u)), \
                 C2(m, y, u) => Succ(use{i}(m, u)) }}\n}}\n"
            ));
        }
        s
    };
    Family {
        name: "forded/occurrences",
        what: "n declarations over one forded family — the per-use cost of fording",
        unit: "uses",
        // Linear, and the fixed cost of declaring the family itself pulls
        // the fit below 1 at the small end (the family costs about as much
        // as one use). A reading above the band means a use started costing
        // more because another use exists.
        expect_slope: Some((0.55, 1.30)),
        cases: sweep("forded/occurrences", &[1, 2, 4, 8], src),
    }
}

/// Form A at a **declared** index (`docs/inductive-fording-lowering.md`
/// §8.2), swept along the number of constructors of the *index* type — which
/// is §14.9's cost dimension exactly: per arm, the inversion emits one tag
/// predicate per **other** index constructor, each a whole `elim_Wf`.
///
/// The data family is deliberately linear (one child), because the measured
/// cliff is the *product* of branching and index width: branching at a
/// three-constructor index already exceeds `DEFAULT_FUEL` and is pinned as a
/// deliberate negative in
/// `crates/elab/tests/indexed_route_2b_declared.rs`. A fixture may not sit
/// at a cliff edge, so this one sweeps the factor that still fits and leaves
/// the falsifier where it is. When the kernel-def round retires that
/// negative, the sweep can gain a branching row and this comment is the
/// pointer to why it did not have one.
fn declared_index_tags() -> Family {
    let src = |n: u64| {
        let mut shape = vec!["SLeaf".to_string(), "SBud(s: Shape)".to_string()];
        for i in 2..n {
            shape.push(format!("SX{i}"));
        }
        format!(
            "inductive Shape {{ {} }}\n\
             inductive Tw : (s: Shape) -> Type {{\n\
             \x20   TL                              : Tw(SLeaf),\n\
             \x20   TB(s: Shape, x: Nat, t: Tw(s))  : Tw(SBud(s)),\n\
             }}\n\
             fn tsize(s: Shape, t: Tw(s)) -> Nat {{\n    \
             match t {{ TL => 0, TB(k, x, u) => Succ(tsize(k, u)) }}\n}}\n",
            shape.join(", "),
        )
    };
    Family {
        name: "forded/declared-index-tags",
        what: "form A at a declared index, swept along the index type's constructor count",
        unit: "index-ctors",
        // ~2.4 measured 2026-08-04 (20 ms → 296 ms from 2 to 6). Quadratic
        // in a quantity the user did not think they were paying for: adding
        // an unrelated constructor to the *index* type makes every arm of
        // every family over it more expensive. §14.9's fuel cliff is this
        // curve hitting `DEFAULT_FUEL`, and a kernel `def` is the recorded
        // fix for both.
        expect_slope: Some((1.80, 3.00)),
        cases: sweep("forded/declared-index-tags", &[2, 3, 4, 5, 6], src),
    }
}
