---
title: Build the ordered field on the ring layers
status: open
labels: [stdlib,mathematics,algebra]
created: 2026-10-20
updated: 2026-10-20
---

`OrderedField<A>(≈, <, ≤, +, *)` (lib/std/ordered_field.hthr) restates the ring
laws as its own fields: `mul_respects`, `mul_assoc`, `mul_comm`, `mul_one`,
`mul_add_distr`, plus the additive group's `zero`, `neg`, `add_zero`,
`add_neg`. The semiring layers (lib/std/semiring.hthr) now state exactly
these, relation-indexed, and `Rat` registers `CommRing<Rat>(Rat::Same, …)`
beside its `OrderedField`. The two do not know each other: a `Ring` theorem
does not apply to an `OrderedField` binder, and `OrderedField::mul_zero` and
`OrderedField::mul_neg` re-prove `Ring::`'s.

Make the ordered layers extend the algebraic ones: `OrderedAddGroup` over
`GroupRel(≈, +)` and `Commutative(≈, +)`, `OrderedField` over `CommRing(≈, +,
*)`, deleting the restated fields and the re-proved theorems. `CReal` then
needs its `CommRing` instance, which its existing lemmas fill.

## What it assumes from elsewhere

- **[[semiring-ring-structure-api]]** owns the layers. Assumed here: their
  field names (`unit`, `inv`, `multiplicative.unit`) are what the ordered
  layers would inherit.
- **[[constructive-ordered-field-interface]]** owns the ordered layers.
