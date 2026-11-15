---
title: Lower tier-1 Wf recursion at the top
status: closed
labels: [recursion,elaboration]
area: language
created: 2026-11-07
updated: 2026-11-07
---

Slice 3 of docs/language/recursion/recursion-at-the-top-design.md §4 (Minus chose option A,
2026-11-04; started 2026-11-07). Recursion at the top on an explicit
parameter of a tier-1 `Wf` inductive (recursive, not codata, indexed, `IWf`,
mutual or infinitary), as the default where the body's first `match` on a
parameter takes it apart and a self-call descends through it, and as the
fallback where the plain lowering refuses, as at `Nat`
([[recursion-at-top-nat-default]]).

## Log

- 2026-11-07: built by hoisting the body's own `match` (design §4, slice 3,
  *As built*). Whole library: 907 recursions at the top (197 before), 30
  attempts falling back; the only change is three expected refusals in
  `recursion_case_split_tests.hthr` (a branch on a parameter the calls
  vary, above a list recursion) that now mean their source, converted to
  acceptances pinned by `refl`. Probes in
  `lib/_tests/std/core/recursion_at_top_tests.hthr` (List and a branching
  tree, the parameter read in its arm, a `let` above, depth two, a call
  under `∃`, a `match` off the result, and a negative control), each
  refused on master, plus a theorem with a hypothesis about the scrutinee
  that master accepts too.
  `List::RecSum_of` is gone from summation.hthr.
- 2026-11-07: `perf ab --base origin/master` first found the default
  costing +21% kernel gate on calc_parser's closure: the rebinding
  `let z: T = C(…)` cost its annotated elaboration and term even unread.
  It is now emitted only where the body reads `z` other than as a
  `match`'s scrutinee (inside the arms too: a first cut that looked only
  outside the arms miscompiled `xs.len()` in an arm, which the
  `recursion_meaning` suite caught; `list_len_read` and `tree_self` pin
  it). Final: counters within 0.1% of master but `cow_copies` (+18%, a
  few hundred), seconds inside the spread; library, showcases and `--pr`
  as on master.
