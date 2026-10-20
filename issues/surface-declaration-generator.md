---
title: Property-test generator over surface declarations
status: open
labels: [elaboration,testing,inductives]
area: infrastructure
created: 2026-07-26
updated: 2026-07-26
---



Split out of [[tyvar-scoping-in-lowered-fields]] step 4, which was found *by
hand* — and that is the point of this issue.

## The gap

The kernel has two generators (`crates/kernel/tests/common/mod.rs` for
scope-only terms, `common/wt.rs` for well-typed ones), and the property
suites built on them are what caught the `Vec^l(T;0)` level defect
([[unit-level-and-vec-preservation]]) and what
[[metatheory-lemma-sweep]] audited ch. 05/06 against.

The **elaborator** has none. Every test in `crates/elab/tests/` is a
hand-written source string. That is fine for acceptance — the acceptance
*is* "this program elaborates and the kernel accepts it" — and it is bad for
the class of bug the two lowering tiers actually have: a rule that is right
on every shape anyone thought to write and wrong on one nobody did.

`tyvar-scoping-in-lowered-fields` is the worked example. The lowering had
been mis-weakening type parameters since tier 0 landed. Nothing caught it,
because every declaration in the suite instantiates its parameters at
*closed* types, where the weakening is the identity. The witness needed
three things at once — a parametric declaration, an instantiation at a
context-dependent type (`=`, the surface's only one), and a preceding field
whose type made the collision type-correct — and no hand-written test was
going to stumble on that conjunction.

## What to generate

Surface `inductive` declarations plus a use, subject to the shape the two
lowering documents describe:

- 0–3 constructors, 0–3 fields each, named and unnamed;
- field types drawn from `Nat`, an earlier declaration, a type parameter,
  and — the one that matters — `=` between terms mentioning the *enclosing
  declaration's* parameters and earlier fields;
- 0–2 type parameters, instantiated at both closed and context-dependent
  types;
- recursive fields, so tier 1's path is covered too (a `Wf`'s shape, arity
  and children tuple all have their own shift arithmetic —
  `docs/inductive-tier1-wf-lowering.md` §5, §6.2).

## The oracle, and why it is not just "it elaborates"

"The kernel accepted it" is necessary and much weaker than what is wanted:
the bug above produced a *kernel-accepted* declaration about the wrong type.
Candidate properties, in rough order of strength:

1. **Round-trip.** Build each constructor and project every field back out;
   the projection must be convertible with what went in. This is the one
   that catches capture — `Mk(3, p)` followed by projecting field 1 must
   give `p`, not something merely of the right shape.
2. **Instantiation commutes.** `⟦D<Ā>⟧` lowered at an instantiation must
   agree with `⟦D<x̄>⟧` lowered at variables and then substituted. Capture is
   exactly the failure of this, and it is the property the bug violated.
3. **Nominal separation.** Two structurally identical declarations stay
   inconvertible (§3.3), which the hand-written suite checks at one pair.
4. **`match` β.** Every generated `match` on a canonical constructor reduces
   to the corresponding arm.

Property 2 is the sharpest and the one to write first: it is a statement
about the *lowering* rather than about the kernel, so it does not depend on
guessing which malformed encodings the kernel would happen to reject.

## Related

- [[elaboration-determinism]] — a different property over the same emitted
  terms.
- The kernel's `common/wt.rs` is the model for how a well-typed generator is
  built here, including the lesson from [[metatheory-lemma-sweep]] that the
  generator's *own* precondition needs an observer: `gen_wt_term` produced an
  ill-typed term at 1 in 3000 and the only check on that was 300 cases on one
  seed stream.
