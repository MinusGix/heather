---
title: Make recursion at the top the lowering for every Nat recursion
status: open
labels: [recursion,elaboration]
area: language
created: 2026-11-04
updated: 2026-11-04
---

Slice 2 of docs/recursion-at-the-top-design.md §4 option A (Minus chose A,
2026-11-04). Today recursion at the top runs only where the plain lowering
refuses or would not mean its source ([[recursion-below-nat-fallback]],
§5). Make it the lowering for **every** structural recursion on an explicit
`Nat` parameter, then delete the Nat guard selection it makes unnecessary:
`guard_param`'s and `outer_case_split`'s Nat cases, the planner's Nat
`ByMeasure`/`Misplaced` routing, and the retry-on-refusal.

Every Nat recursion's term changes (one more match at the top, the
generalized motive, the static arm choice), so this is a measured round:
`scripts/perf ab` over the library corpus before it lands, counters first.
Choosing the decreasing parameter becomes a search over the explicit Nat
parameters (the planner's guess first).

## Acceptance

- Every library module checks with `--expectations`, with
  `recursion-meaning` (`--review`) clean or no worse than master.
- `perf ab`: no counter regression the report cannot explain; seconds
  inside the spread.
- The Nat guard-selection code is deleted, with its probes
  (`recursion_case_split_tests.hthr`) still passing or converted to
  acceptances with their meanings pinned by `refl`.
