---
title: Build the ordered field on the ring layers
status: closed
labels: [stdlib,mathematics,algebra]
area: mathematics
milestone: [math-classes]
created: 2026-10-20
updated: 2026-10-21
---

`OrderedField<A>(≈, <, ≤, +, *)` (lib/std/algebra/ordered_field.hthr) restates the ring
laws as its own fields: `mul_respects`, `mul_assoc`, `mul_comm`, `mul_one`,
`mul_add_distr`, plus the additive group's `zero`, `neg`, `add_zero`,
`add_neg`. The semiring layers (lib/std/algebra/semiring.hthr) now state exactly
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

## Log

- 2026-10-21: done. `OrderedAddGroup` extends `GroupRel(≈, +)` + `Commutative(≈, +)` (zero `A.unit`, negation `A.inv`); `OrderedField` extends `LocatedAddGroup` + `CommRing(≈, +, *)` (one `A.multiplicative.unit`). The restated fields and the re-proved `zero_add`, `neg_add_self`, `neg_unique`, `neg_neg`, `add_add_add_comm`, `one_mul`, `mul_zero`, `mul_neg`, `neg_mul`, `neg_mul_neg` are gone; the field's inverse is `recip` (law `mul_recip`, theorems `recip_*`) because `inv` is now the additive group's. The additive `GroupRel` reached through both parents is one untagged fiber, so no class-system change was needed. `CReal` registers `CommRing` from its lemmas plus `one_mul`, `zero_mul`, `neg_add_self`. Design: docs/constructive-ordered-field-design.md, "Built on the ring layers".
