---
title: Connect ordered structures to addition and multiplication
status: closed
labels: [stdlib,mathematics,order,algebra]
area: mathematics
milestone: [math-classes]
created: 2026-09-02
updated: 2026-11-02
---

Factor the compatibility laws between order and algebra: translation
invariance/monotonicity of addition, monotonicity of multiplication by a
nonnegative factor, positivity, and the ordered-ring/ordered-field composites
that real-number interfaces need.

Do not choose one giant `OrderedRing` prematurely. Probe which compatibility
theories are independently consumed by `Nat`, `Int`, rationals, absolute
value, and interval reasoning, and preserve constructive strict/non-strict
distinctions.

## What it assumes from elsewhere

- **[[mathematical-order-hierarchy]]** owns order laws.
- **[[semiring-ring-structure-api]]** owns ring laws.

## Log

- 2026-09-02: Filed as the bridge rather than folding order into the ring
  hierarchy itself.
- 2026-10-19: First consumer: [[constructive-ordered-field-interface]] composes order with + (OrderedAddGroup: translation-invariant <, ≤ translation without locatedness) and * (OrderedField: mul_pos, strict monotonicity derived) over a setoid, in lib/std/algebra/ordered_field.hthr.
- 2026-11-02: Landed (docs/library/ordered-algebra-design.md). Rechecked against the library first. The field half had been built (`StrictOrder` up to `OrderedField`), but nothing below the field joined order to `+` and `*`: `Nat` and `Int` had no instance, so `big_operator` carried hand copies of `range_le`, and the multiplication theorems sat at `OrderedField` though none needed the reciprocal. New layers in `lib/std/algebra/ordered_field.hthr`:
  - `OrderedAddMonoid`: translation keeps and reflects `<`. Reflection is a law here because a monoid has no inverse to add.
  - `LocatedAddMonoid`: adds cotransitivity.
  - `OrderedSemiring`: `0 < 1`, and a positive factor keeps and reflects `<`. These are the monotone forms, because `mul_pos` gives nothing without subtraction.
  - `OrderedRing`: semiring plus located group, with no fields of its own.
  - `OrderedField` now extends `OrderedRing` and keeps only `recip`, `of_nat` and `archimedean`.

  Each theorem moved to the weakest class it needs. `mul_le_mono_l` now goes by tightness (a refutation) instead of subtraction, and `pos_of_mul_pos_nonneg` by cotransitivity without negation. Instances: `Nat` (semiring) and `Int` (ring) at the end of the module, `Dyadic` (ring) in dyadic.hthr; `Rat` and `CReal` fill the new laws through their field instances. `Nat::range_le` and `Int::range_le` now call `LocatedAddMonoid::range_le`, and `mono` has a class row per layer. Answers to the probe question:
  - `Nat` consumes the monoid and semiring layers.
  - `Int` and `Dyadic` consume the ring.
  - Absolute value needs the located group.
  - Intervals stay at the field for division; containment for `+` and `*` could drop to the ring, design §5.

  Strict and non-strict stay as `StrictOrder` has them. Probes and refusal controls are at the end of `lib/_tests/std/algebra/ordered_field_tests.hthr`.
