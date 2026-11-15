---
title: Make Rat's and CReal's division the ordered-field class's
status: open
labels: [stdlib,mathematics,notation]
area: mathematics
milestone: [math-classes]
created: 2026-11-06
updated: 2026-11-06
---

`/` and `⁻¹` are stated once over `OrderedField` (lib/std/algebra/field_division.hthr,
docs/library/division-design.md §6), and a carrier reads the generic laws through its
instance by unfolding: `OrderedField::div_mul_cancel(a, b, h := Inr(hb))` proves
`a / b * b ≈ a` at `Rat` (lib/_tests/std/algebra/field_division_tests.hthr).
But `Rat` and `CReal` still keep their own `div`, `inv`, laws and sign rules
(`Rat::Positive`, `Rat::apart_mul`, …), each a copy of the class's.

Retiring the copies means a carrier's `/` *is* the class's at its instance, so
one search at `Invertible` serves every field. What stands in the way:

- The carrier-only producers: computation for a closed divisor (`1 / 2`), and at
  `Rat` the `Nonzero` rule (`¬(b ≈ 0)`, not constructive at the class).
  They would become rules keyed at `Invertible` at the carrier.
- `ring` and `linarith` read `Rat::div`/`Rat::inv` through the carrier's
  designations, and numeral reciprocals (`a / 2`) through `Rat::positive_inv`.
- Cost: a generic rule's application carries the instance dictionary; at a
  closed carrier every proposal's check unfolds it.
- Clients cite `Rat::div_mul_cancel` and friends by name; they would stay as
  aliases of the class's.

Not urgent: nothing is missing at either carrier, only duplicated.
