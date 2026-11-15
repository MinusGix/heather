---
title: Read a written 0 < e through the one-place sign predicates
status: closed
labels: [proofs,solver,arithmetic]
area: tactics
milestone: [tac-arith]
created: 2026-11-06
updated: 2026-11-06
---

The sign rules at `Rat` and `CReal` are about one-place predicates
(`x.Positive()`, `x.Negative()`, `x.NonNeg()`, `x.Nonzero()`) because
Paterson's condition refuses a rule from `0 < x` to `x.Apart(0)`
(docs/library/inverse-power-notation-design.md §3, docs/library/division-design.md §3). A
*local* `0 < x` reaches them by conversion. A *goal* written `0 < e` does
not: the search looks for rules about `Rat::Lt`, finds none, and stops.

```heather
theorem t(a, b: Rat, ha: 0 < a, hb: 0 < b): 0 < a / b { positivity }        // refused
theorem t(a, b: Rat, ha: 0 < a, hb: 0 < b): (a / b).Positive() { positivity }  // proved
```

Wanted: a way for a carrier to say "a goal `0 < e` is `e.Positive()`" (and
`e < 0`, `0 <= e`), read by `infer` and `positivity` before reporting
no-rule: the converse of the unfolding step that turns `x.PowOk(n)` into
`x.Apart(0)` (docs/library/inverse-power-notation-design.md §4). A view is
Paterson-free because it is a conversion, not a rule. `Nat`'s rules are
about `Nat::Lt` directly, so this is the fields' gap.

## Log

- 2026-11-06: Done without a view mechanism: the rules `lt_of_positive`, `lt_of_negative`, `le_of_nonneg` (from the one-place predicate to the written relation) pass Paterson's condition in that direction, so `positivity` at `0 < a / b` and `h: 0 < e := infer` reach the sign rules (probes in rat_tests).
