---
title: Stress-test transfer through dependent families
status: open
labels: [stdlib,relations,dependent-types,design]
created: 2026-09-04
updated: 2026-09-05
---

Promote a small dependent example early so a successful first-order transfer
API does not hide a failure around indexed data. This issue owns the required
fiber structure and its laws, not a universal dependent framework in round one.

For `x ≈ y`, the types `B(x)` and `B(y)` do not automatically become identical.
Specify relations between fibers; where constructing values requires transport,
provide transport operations with identity/composition laws in the chosen
fiber relation. State whether these depend on the witness of `x ≈ y`, and
require coherence or witness independence only where the customer needs it.

## Acceptance

- Choose an indexed family with genuinely distinct but related indices; a
  constant family or rewriting only by identity is insufficient.
- Derive a dependent function compatibility rule and a dependent-pair relation,
  then prove the laws needed by one transported operation/theorem.
- Include evidence-dependent content with the subtype owner. Distinguish a
  relational comparison from an actual map between fibers and from identity
  transport; document precisely what each example consumes.
- Record unsupported elimination contexts and their missing structure in a
  form the generator can report as goals. Include one successful dependent
  rewriting example to assess practical ergonomics against quotient usage.

## What it assumes from elsewhere

- **[[relational-transfer-core]]** owns nondependent transfer.
- **[[subtype-transfer-and-evidence]]** owns evidence policy and its customer.
- **[[setoid-auto-lifting]]** owns generated compatibility proofs.
- **[[certified-parametricity]]** owns dependent parametricity generation.

## First dependent customer

**[[finite-set-client-design]]** proposes `Element(xs) = Σ a. Mem(a,xs)`.
Set equivalence supplies membership maps, hence actual transport between these
fibers. Forward/backward maps are inverses modulo the relation on underlying
values, without requiring round-trip identity of membership proofs. Compare
two equivalence witnesses and include a witness-inspecting negative control.
This example exercises genuinely varying fibers but does not settle arbitrary
indexed families; cardinality-indexed vectors remain a stronger later probe.

## Log

- 2026-09-04: Filed from the setoid and general transfer design discussion.
- 2026-09-04: Selected membership-bearing elements of equivalent finite sets as an early concrete dependent example.
- 2026-09-05: Added the narrow witness-subtype probe: Fin indexed by the retained bound exposes why SameNumber alone cannot justify identity transport. This is a refusal boundary, not the successful dependent transport/coherence customer required by this issue.
