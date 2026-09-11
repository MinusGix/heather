---
title: Measure and bound relational search and generated proof cost
status: open
labels: [setoids,design,backlog]
created: 2026-09-05
updated: 2026-09-11
---

The present derivation has traversal bounds, but a useful cost story also needs proof size, conversion work, and certificate reuse. This is separate from the representation cost of large dependent dictionaries.

## Acceptance

- Measure visited nodes, reduction steps, certificate probes, emitted proof size, and kernel checking on composed and shared subexpressions.
- Show how costs scale with nesting, repeated uses, branches, and opaque certificate boundaries. Include refusal at exhausted budgets without claiming the theorem false.
- If memoization is introduced, key it by the actual environment, operation, relations, assumptions, and binder scope; test invalidation and proof-relevant evidence distinctions.
- Preserve sharing where useful and recheck reused artifacts. Separate cold/warm search costs from kernel conversion costs.

Customers: named augment and conditional augment on both backends. Related: [[relational-certificate-registration]], [[setoid-dictionary-projection-growth]], [[proof-benchmark]], [[setoid-auto-lifting]].

## Scheduling

Captured for a future concrete driver; not scheduled by this filing. See [[setoid-roadmap-and-resumption]].

## Log

- 2026-09-11: 2026-09-11 datum: lib_setoid_mergeable is the slowest fast-lane target at ~50 s on the furnace box, and a per-worker semantic-image memo (one replay instead of 28) did not move it (48.2 -> 50.0 s), so the cost is the 28 tests' own elaboration over the relation/algebra_rel/list_setoid prefix, not prefix replay. Next action when it matters: --item-timings-style attribution per test (see [[perf-instrumentation-consolidation]]).
