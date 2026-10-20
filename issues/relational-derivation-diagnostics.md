---
title: Explain relational derivation failures at the responsible expression
status: open
labels: [setoids,design,backlog]
area: tactics
created: 2026-09-05
updated: 2026-09-05
---

Current compatibility, branch_choice, and definition goals are useful but should explain what the function observes or changes, without exposing generated names as the primary explanation.

## Acceptance

- Point to the responsible operation, condition, or unsupported construct in the named function, with the call path from the explicit request.
- Show the exact input/output relations, required assumptions, and an ordinary way to provide the missing proof.
- Distinguish missing evidence, ambiguous evidence, unsupported syntax, and resource exhaustion. Preserve independent goal identities across requests and rechecks.
- Offer structured records to tooling, with source locations and bounded summaries; use an optional checked counterexample only to justify an actual refutation.

Customer: remove the stability premise from `conditional_compatible` in `docs/showcase/derive_set_functions.hthr`. Specializes [[ai-facing-tooling]] for [[setoid-auto-lifting]]; related: [[diagnostics-name-the-written-form]], [[relational-rewrite-controls]], [[heather-disprove]].

## Scheduling

Captured for a future concrete driver; not scheduled by this filing. See [[setoid-roadmap-and-resumption]].
