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
//! | `forded/declared-index-branching` | ditto at a **branching** index constructor | §14.9 |
//!
//! **The bands record the exponents that exist, not the ones the design
//! wants**, which is the kernel doc's rule for a band that records a defect
//! (docs/benchmarking.md, "Adding a family").
//!
//! Re-recorded 2026-08-04 by `issues/generated-term-defs.md`, and the result
//! is not the one the phase-1 comment predicted. Routing `μ`, the index type's
//! tag predicates and its child projections through Ψ definitions cut the
//! **constant** by 4–7× on the first two families and 1.35× on the third — and
//! moved the **exponents** by 0.6, 0.0 and 0.0. So `--check` never went red:
//! the fits stayed inside bands written to record a defect that turned out to
//! be two defects sharing a curve.
//!
//! What is left is not the generated *terms* but the generated **types**. A
//! forded family's skeleton `⟦Skel⟧` and its index type `I` are `Type::Wf`s
//! whose node count is Θ(constructors), and they are written out afresh at
//! every occurrence — once per `sEq`, per `Lam` domain, per `transp`
//! annotation, per motive instantiation, of which there are Θ(constructors).
//! Θ(n) copies of a Θ(n) type is the residual quadratic, and it is not
//! reachable by the same lever: `GlobalBinding::Ty` has no body, so a *type*
//! cannot be a Ψ definition at all. See `docs/inductive-fording-lowering.md`
//! §14.11.
//!
//! The bands below are therefore tightened around the new exponents rather
//! than moved: they claim what this round measured, and the next round's
//! target is the constant they sit on top of.

use crate::harness::Family;
use heather_elab::IndexedRoute;

use super::scale::indexed_sweep;

const ADD: &str = "fn add(a: Nat, b: Nat) -> Nat { match b { Zero => a, Succ(k) => Succ(add(a, k)) } }\n";

pub fn families() -> Vec<Family> {
    vec![computed_arms(), occurrences(), declared_index_tags(), declared_index_branching()]
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
        // 2026-08-05, `issues/family-types-as-code-defs.md`: the emitted
        // *types* became `El (code^δ)` references — 2.79 → 2.54 and ~0.6× on
        // the constant. What is left quadratic is the `Supf`/`ElimWf`
        // **shape** slots, which carry the `Wf`'s shape component and no
        // registered code names (`docs/inductive-fording-lowering.md`
        // §14.11's closing note). Band tightened around the measured slope.
        what: "a route-2b family with n constructors, and the n-arm match over it",
        unit: "arms",
        // **3.39 → 2.82**, and 31 ms → 8.5 ms at 2 arms / 1.25 s → 195 ms at
        // 6 (`issues/generated-term-defs.md`, 2026-08-04). `μ` is now one Ψ
        // definition referenced per arm instead of a whole `elim_Wf` written
        // out per arm, which is the 6.4× at the wide end; the exponent moved
        // only 0.6 because the *skeleton type* is still inlined Θ(n) times
        // and is itself Θ(n) (the module header, §14.11). Band tightened from
        // 2.60–4.00 to claim the new slope.
        //
        // 2026-08-17, re-recorded: **2.19** (six runs, range 2.18-2.22),
        // against an old floor of 2.20 -- i.e. the gate was decided by the
        // third digit of a fit. Re-centred on the measurement +/-0.35.
        expect_slope: Some((1.85, 2.55)),
        cases: indexed_sweep(
            "forded/computed-arms", &[2, 3, 4, 5, 6], "F", IndexedRoute::Iwf, src,
        ),
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
        //
        // The slope was never the point here and did not move (1.03 → 1.01).
        // The **per-use** figure did, and it is this round's headline: 119 ms
        // → 29 ms per mention of a forded family
        // (`issues/generated-term-defs.md`, 2026-08-04). That is `μ` stopping
        // being a whole `elim_Wf` in every type that names the family.
        // 2026-08-05: ~28 ms → ~19 ms per use (the code-reference round);
        // slope ~1.0 unchanged, as designed. Band floor raised now that two
        // rounds have measured it at 0.99–1.01.
        expect_slope: Some((0.70, 1.30)),
        cases: indexed_sweep(
            "forded/occurrences", &[1, 2, 4, 8], "F", IndexedRoute::Iwf, src,
        ),
    }
}

/// **Not a forded family.** Corrected 2026-08-06, and the misattribution is
/// the finding: `Tw`'s two constructors state their indices as *patterns*
/// (`Tw(SLeaf)`, `Tw(SBud(s))` with `s` a field), and the classifier tries
/// route 1 **first** (`inductive.rs::classify_indexed_route`), so this
/// declaration has never had a skeleton, a `μ`, or a form-A inversion. It is
/// `docs/inductive-indexed-lowering.md` §8.2 — route 1 at a declared index —
/// swept along the index type's constructor count, which is that scheme's own
/// cost dimension: the family node carries one branch per index constructor
/// and is re-emitted per occurrence.
///
/// Two rounds read this family as route 2b and drew conclusions from it. The
/// 2026-08-04 term round explained its flat exponent by "the index type is
/// Θ(n) and a type cannot be a Ψ definition"; the 2026-08-05 code round
/// explained the exponent *still* not moving by a third defect in the
/// `Supf` shape slots of a form-A inversion this declaration does not have
/// (`issues/wf-shape-annotation-slots.md`). Neither round's lever touched it,
/// which is exactly why it did not move — and the route-1 round moved it at
/// once. The lesson for a fixture: name the route the classifier picks, not
/// the route the source looks like. The family **name** is left alone because
/// it is the baseline's key; renaming it is a coordinator's call.
///
/// The name's original claim, for the record: per arm, a form-A inversion
/// emits one tag predicate per **other** index constructor, each a whole
/// `elim_Wf` (§14.9). That cost is real; it is measured by
/// [`declared_index_branching`] below, which *is* forded.
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
        // **2.65 → 2.66**, and 18 ms → 13 ms at 2 / 328 ms → 241 ms at 6
        // (`issues/generated-term-defs.md`, 2026-08-04). The tag predicates
        // and child projections became Ψ definitions, which is the 1.35×; the
        // exponent did **not** move, because what is quadratic here is the
        // *index type* — Θ(n) nodes, written out Θ(n) times, and a type cannot
        // be a Ψ definition (§14.11 / the module header). This is the family
        // that says the round's lever and the round's curve are not the same
        // thing. Band tightened from 1.80–3.00 around the measured slope.
        //
        // 2026-08-05, `issues/family-types-as-code-defs.md`: the code
        // definitions landed and the slope did **not** move again (2.61 →
        // 2.62), while every other forded family improved. The claim that
        // round made — below 2.0 — is NOT met and is not absorbed here: the
        // residual is a *third* defect, the `Supf` the inversion rebuilds per
        // index branch (`zj`), whose `shape` annotation is the index type's
        // Θ(n) shape component and is instantiated Θ(n) times per arm — no
        // registered code names a `Wf`'s *shape*, only the whole `Wf`
        // (`docs/inductive-fording-lowering.md` §14.11's closing note,
        // `issues/wf-shape-annotation-slots.md`). Band records the exponent
        // that exists, per the suite's rule.
        //
        // 2026-08-06, phase 5: **2.79 → 2.19**, and 17.0 ms → 10.5 ms at 2 /
        // 294 ms → 118 ms at 6 (2.5× at the wide end). The lever was route
        // 1's `D#fam`, because this family is route 1 — see the doc comment
        // above. The two paragraphs before this one are what a fixture's
        // wrong label costs: two rounds' worth of explanation for a curve
        // whose cause was never in either round's reach.
        //
        // 2026-08-17, re-recorded: **1.06** (six runs, range 1.02-1.08). This
        // is the one large move of the re-record -- 2.19 -> 1.06 -- and it is
        // not this suite's doing: nothing in the fixture changed, and the
        // exponent was already 1.09 at HEAD on 2026-08-16. The kernel-side
        // rounds since 2026-08-06 took the wide end of this family, and the
        // attribution paragraphs above are day-of records rather than current
        // explanations. What the band guards is unchanged: a power coming
        // back.
        expect_slope: Some((0.75, 1.45)),
        cases: indexed_sweep(
            "forded/declared-index-tags", &[2, 3, 4, 5, 6], "Tw", IndexedRoute::One, src,
        ),
    }
}

/// [`declared_index_tags`] at a **branching** index constructor — the row
/// §14.9's fuel cliff used to forbid.
///
/// `SNode(l, r)` has two children, so each form-A arm recovers two child-index
/// binders through two child projections, and the emitted eliminator is the
/// *product* of that with one tag predicate per other index constructor. Until
/// 2026-08-04 that product blew `DEFAULT_FUEL` at three index constructors
/// (`crates/elab/tests/indexed_route_2b_declared.rs`, then a deliberate
/// negative and now a positive), which is why the sweep above is linear and
/// why this one could not exist.
///
/// First measured 2026-08-04, after the definitions landed, with the
/// pre-definition numbers taken on the same machine for the comparison:
/// 353 ms → 110 ms at 2 index constructors and 2.08 s → 556 ms at 6, i.e.
/// 3.2–3.7× and a slope of ~1.47. Note the slope is *below* the linear
/// family's 2.66: `BDup`'s non-linear result index makes it a form-B arm, and
/// a form-B arm has no per-index-constructor inversion to pay for. The band is
/// wide because this is one machine on one day.
fn declared_index_branching() -> Family {
    let src = |n: u64| {
        let mut shape = vec!["SLeaf".to_string(), "SNode(l: Shape, r: Shape)".to_string()];
        for i in 2..n {
            shape.push(format!("SX{i}"));
        }
        format!(
            "{ADD}inductive Shape {{ {} }}\n\
             inductive Bl : (s: Shape) -> Type {{\n\
             \x20   BLeaf                                            : Bl(SLeaf),\n\
             \x20   BNode(l: Shape, r: Shape, dl: Bl(l), dr: Bl(r))  : Bl(SNode(l, r)),\n\
             \x20   BDup(s: Shape)                                   : Bl(SNode(s, s)),\n\
             }}\n\
             fn count(s: Shape, d: Bl(s)) -> Nat {{\n    \
             match d {{ BLeaf => 1, BNode(l, r, dl, dr) => add(count(l, dl), count(r, dr)), \
             BDup(s) => 0 }}\n}}\n",
            shape.join(", "),
        )
    };
    Family {
        name: "forded/declared-index-branching",
        what: "form A at a branching declared index, swept along the index type's constructor count",
        unit: "index-ctors",
        // 2026-08-05: constants ~0.75× under the code-reference round, slope
        // 1.53 → 1.57 (within the machine's spread). Band tightened.
        //
        // 2026-08-17, re-recorded: **1.27** (six runs, range 1.24-1.31). Not
        // an exit -- the old 1.20 floor held -- but by 0.04, which is inside
        // the family's own range, so it was one round away from being one.
        expect_slope: Some((0.90, 1.65)),
        cases: indexed_sweep(
            "forded/declared-index-branching", &[2, 3, 4, 5, 6], "Bl",
            IndexedRoute::Iwf, src,
        ),
    }
}
