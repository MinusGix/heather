---
title: All-numeral relations elaborate at Nat silently
status: open
labels: [frontend,elaboration,notation,ergonomics]
area: language
created: 2026-10-20
updated: 2026-11-06
---

A relation whose operands are all numerals has no carrier, so it elaborates
at `Nat` by the numeral default, and nothing says so. Found moving `Rat` and
`CReal` onto numerals ([[rat-numerals-and-semigroup-clash]]): with
`Rat::zero()`/`Rat::one()` retired, the old statement
`Rat::zero() < Rat::one()` became

```heather
theorem Rat::zero_lt_one(): 0 < 1 { omega }
```

which checked: it states `Nat`'s `0 < 1`, `omega` proves it, and the
`OrderedField<Rat>` instance's `zero_lt_one := Rat::zero_lt_one()` field still
converted, because both `Nat::Lt(0, 1)` and `Rat::Lt(0, 1)` compute to the same
closed proposition. Only `CReal`'s copy failed, at the kernel, with no surface
spelling for either side. Test sources had the same shape inside `let gap: (0 < 1)
= omega;`, where a refusal test would then have been refused for the wrong
reason.

The library now spells these `Rat::Lt(0, 1)`, `CReal::Same(0 + 0, 0)`; the
spelling is honest but it is the one place numerals do not read as
mathematics.

A second, narrower shape: a `calc` chain whose first two endpoints are
numerals (`calc { 0 ≈ 0 + 0 := …, < x + y := … }`) refuses, because the
desugared `relation_step(≈, e0, e1, e2, …)` checks `e0` against the carrier
metavariable before `e2` could solve it. A single numeral first endpoint
followed by a non-numeral one already works (the sibling-operand probe in
`dispatch/operator.rs`).

## Acceptance

- An all-numeral operand list under a relation designated at more than one
  carrier is at least a warning naming the carrier it chose, or is refused
  with the designated carriers listed — not a silent `Nat`.
- Or: a relation-typed position with an expected proposition (an instance
  field, a `let` annotation, a calc's expected type) passes its carrier down.
- A calc chain's leading numeral endpoints take the carrier of the first
  non-numeral endpoint.

## Log

- 2026-10-27: Related, filed 2026-10-27: [[numeral-normalisation]] (norm_num at every numeric carrier) needs this issue's answer for which carrier a relation means.
- 2026-11-06: The same default reaches terms now that `/` is designated at
  `Rat` (docs/division-design.md): `1 / 2` with no expected carrier is
  `Nat` division, `0`, silently; `let x: Rat = 1 / 2` is ½. A refusal or a
  warning at an all-numeral `/` whose `Nat` value truncates would catch it.
