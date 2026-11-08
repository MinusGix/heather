---
title: Numerals, prefix minus and subtraction at a class-section carrier
status: open
labels: [notation,traits,stdlib,ergonomics]
area: mathematics
milestone: [math-classes]
created: 2026-11-08
updated: 2026-11-08
---

Inside `section<K: OrderedField(≈, <, <=, +, *)>` the carrier has `+`, `*`,
`<`, `<=`, `≈`, and since 2026-11-06 `x⁻¹` and `a / b` (designations at the
class, lib/std/algebra/field_division.hthr). It has no `0`, `1`, `2`, no
`-x` and no `x - y`. Probes:

```heather
theorem p_neg_ok(x: K): x + -x ≈ K.unit { K.inv_r(x) }
// `-` has no meaning here: no `designation prefix - at …` covers this carrier
theorem p_zero_lt(x: K): K.unit < 1 { K.zero_lt_one }
// this has type `Nat`, but `K` is expected here
theorem p_sub_ok(x, y: K): x - y ≈ x + K.inv(y) { K.rel_refl(x + K.inv(y)) }
// `-` has no meaning here
```

So every generic statement is spelled through the dictionary: in lib/std,
`K.unit` 353 times, `.multiplicative.unit` 656 times, `K.inv(` 489 times,
and constants as `K.of_int(OfNat(2))` or `1 + 1`. Compare
`OrderedField::half_pos(e: K, he: K.unit < e): K.unit < OrderedField::half(e)`
with what it means, `0 < e → 0 < e / 2`. This is the single largest
difference between the generic analysis files (real_fn, sequence,
closed_interval, supremum) and the same mathematics at `Rat`/`CReal`.

## Direction

- **`-` both ways is a library change**: `designation prefix - at
  OrderedAddGroup := …` and `designation - at OrderedAddGroup := …` beside
  the two in field_division.hthr (rung 2b of
  docs/operators-onto-classes-design.md §4). Check the precedence the
  designation at a class gets against a carrier's own (`Rat`'s designation
  must still win at `Rat`).
- **Numerals need the language**: a numeral checked at a carrier with no
  `Numeral` instance but a dictionary in scope that names its integers
  (`CommRingOfInt`'s `of_int`, or `OrderedField`'s `of_nat`) elaborates as
  that embedding, `0` and `1` as the dictionary's units so nothing
  changes definitionally for the tactics. The [[carrier-directed-numerals]]
  route is the place; [[class-carrier-division-gaps]] already lists the
  numeral gap as one of its three bullets and keeps its other two.
- `linarith` at a class carrier then needs to read `e / 2` as `½·e`: today
  it refuses `e / (1 + 1) < e` from `0 < e` and `0 < 1 + 1` at `K` (it
  proves the same at `Rat`), naming `div(e, …)` an atom.

## Acceptance

- The three probes above check, and a fourth: `0 < e → e / 2 < e` by
  `linarith` at `K`.
- `real_fn.hthr`'s bound lemmas (`two_pos`, `half`, `half_add`, `half_pos`,
  `half_lt`, `shrink`) are restated with numerals; `half` itself becomes
  `e / 2` or goes.
- Negative control: at `Rat` and `CReal` numerals and `-` elaborate to the
  same terms as before (`scripts/timings --diff` count columns unchanged on
  rat.hthr and creal.hthr).

## Related

[[infix-subtraction-notation]] (the carrier half), [[class-default-operators]],
[[casting-standard]]; docs/stdlib-math-awkwardness-survey.md §2.
