---
title: Conjunction field chains still traverse their remaining types during elaboration
status: open
labels: [elaboration,performance,proofs]
created: 2026-09-28
updated: 2026-09-28
---

The kernel prefix replay is fixed by [[conjunction-projection-chain-cost]],
whose evaluator-step family is now linear. Source checking remains
superlinear: field preparation substitutes through the remaining structural
tail and spells the selected field at every source dot. A selected `.right`
field is itself the next large conjunction, so those traversals overlap.

Reproduce with `probes/conjunction_projection_chain.py`; compare using
`scripts/perf ab --file target/conjunction-chain.hthr:lib/std` and inspect
`decl_body_ns` separately from the kernel gate. Keep the bare-parameter and
opaque-theorem-alias variants, open element types and dependent-field controls.

On 2026-09-28, the post-fix bare family at depths 8/16/32/64 has evaluator
steps 84/180/372/756 but `shift_global_nodes` 1667/7067/29387/120107. Those
rescoping counts include elaboration's naming probes as well as the gate;
they are not a kernel-only counter. The source-side type walks still dominate
large items. The measured A/B was under host load, so it establishes exact
counter shapes, not a clean wall-time exponent.

Investigate whether carrying structural type components with deferred local
substitution can avoid re-traversing the suffix. Do not widen named-projection
receiver policy without the controls owned by
[[per-instantiation-projection-boundaries]].

## Acceptance

Attribute the remaining structural substitution, emission and instance-matching
traversals separately, then reduce their repeated work on this family without
changing field identity or dependent substitution. Measure a current library
customer as well as the synthetic chain before choosing a representation change.
