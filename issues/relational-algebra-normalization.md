---
title: Normalize relational algebra expressions with checked law certificates
status: open
labels: [setoids,design,backlog]
created: 2026-09-05
updated: 2026-09-05
---

Current calc and rel_cong proofs still spell out associativity, commutativity, and idempotence rearrangements. A bounded normalizer could remove that repetition when a real proof workload warrants it.

## Acceptance

- Select the operation, relation, and exact available laws explicitly. Distinguish associative, commutative, idempotent, and unit-bearing cases.
- Emit ordinary checked equality-of-meaning proofs; preserve multiplicity when idempotence is absent and do not invent a unit.
- Exercise nested contexts and a user-defined law interface, with negative controls for missing laws and a different operation on the same carrier.
- Report unsupported operators or exhausted budgets usefully, and measure proof size/checking cost rather than only source brevity.

Customer: `union_interchange` and `extend_stable` in `docs/showcase/finite_set_client.hthr`. Related: [[relation-indexed-algebra]], [[relational-rewrite-controls]], [[setoid-auto-lifting]], [[relational-derivation-cost]].

## Scheduling

Captured for a future concrete driver; not scheduled by this filing. See [[setoid-roadmap-and-resumption]].
