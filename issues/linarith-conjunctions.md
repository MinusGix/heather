---
title: linarith reads conjunctions and the bounds that unfold to them
status: closed
labels: [tactics,arith,ergonomics]
area: tactics
milestone: [tac-arith]
created: 2026-11-06
updated: 2026-11-06
---

`linarith` and `nlinarith` read only `<`, `<=`, `≈` and `¬(x < y)`. The
analysis library states its bounds as predicates that unfold to
conjunctions (`AbsLe`, `AbsLt`, `Close`, `Between`, `Within`), so every
client split them by hand: `linarith(hz.left, hz.right)` for a fact, and
`LocatedAddGroup::abs_le_intro(z, e, linarith(…), linarith(…))` for a goal.
The library had 94 `.left`/`.right` arguments inside `linarith` calls and
38 `abs_le_intro` wrappers.

Wanted (docs/linarith-design.md §9):

- A written or context fact that is a conjunction, or whose head unfolds to
  one, gives each side as a row (field route and `Int`/`Nat` route).
- A goal that is one, or unfolds to one, is proved side by side.
- A refusal names the failing side as a side of the goal as written.

## Log

- 2026-11-06: Built (docs/linarith-design.md §9). Probes in
  `lib/_tests/std/tactic/linarith_tests.hthr` (`conj_*`). The library sweep
  dropped the 12 `abs_le_intro` calls whose sides were both `linarith` calls
  and merged `.left`/`.right` pairs in `real_fn.hthr` and
  `real_fn_limit.hthr`. The context pass had been silently dropping the
  context's literal conjunctions (a projection's name does not resolve);
  it now reads their evidence directly. Left for later: `Rat::abs`/`CReal::abs`
  as functions, `∨` facts, `↔`.
