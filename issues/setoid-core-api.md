---
title: Add a small relation-indexed setoid core
status: open
labels: [stdlib,mathematics,setoids,relations]
created: 2026-09-02
updated: 2026-09-04
---

Introduce the minimum explicit API for reasoning modulo an equivalence
relation. Keep the first round manual: automation must reproduce successful
mathematical constructions rather than determine their semantics.

## Acceptance

- Reuse `Equivalence(R)`; no canonical global relation is chosen for a carrier.
- Expose convenient unary/binary respectfulness through the shared function
  relator. Prove the basic composition rules and use identity as a control.
- Define morphisms as respectful functions with certificates. Compare their
  underlying functions pointwise modulo the target relation, without asking
  for function identity or equality of certificate fields. Establish the
  equivalence laws on respectful functions, not arbitrary raw functions.
- Exercise unreduced rationals and a function-valued or proof-bearing
  representation. Rational arithmetic must respect equivalence; denominator
  extraction must fail as an invariant Nat-valued observation.
- Keep bundles, coercions, and notation policy out of this first round.

## What it assumes from elsewhere

- **[[relation-property-structures]]** owns equivalence-relation laws.
- **[[relational-transfer-core]]** owns heterogeneous respectful signatures.
- **[[relation-indexed-algebra]]** owns algebraic laws modulo a chosen relation.
- **[[setoid-auto-lifting]]** owns future proof generation, unnecessary here.
- **[[subtype-transfer-and-evidence]]** owns subtype evidence policy.

## Log

- 2026-09-02: Filed as a quotient substitute at abstraction boundaries, not a
  replacement for ordinary identity throughout the library.
- 2026-09-04: Expanded from the agreed relational-transfer design; implementation remains open.
- 2026-09-04: **[[manual-mergeable-round]]** implements the shared respectful-function foundation and a membership-based list customer. This does not complete the rational, morphism, or function-valued acceptance owned here.
