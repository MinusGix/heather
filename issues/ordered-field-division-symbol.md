---
title: State division once over the ordered-field classes
status: open
labels: [stdlib,mathematics,notation]
area: mathematics
milestone: [math-classes]
created: 2026-11-06
updated: 2026-11-06
---

`/` and `⁻¹` are designated at `Rat` and `CReal` with a searched
apartness (docs/division-design.md), each carrier restating the same
definitions, laws and sign rules. The generic classes have
`OrderedField::recip(x, h)` but no symbol, so a section over
`A: OrderedField(…)` writes `x * A.recip(x, h)` and passes `h` by hand.

Wanted, in order:

1. `⁻¹` and `/` inside a section over an ordered field, at the
   dictionary's `recip` with `h: ApartBy(<, x, A.unit) := infer` (needs a
   designation, or a binder symbol, for a postfix operator and a defaulted
   proof at a class carrier; docs/operators-onto-classes-design.md).
2. The division laws (`div_mul_cancel`, `div_respects`, `add_div`, …)
   and the sign rules stated once there, with `Rat`/`CReal` reading them
   through the instance; the carrier copies then go.
3. The `nlinarith` search rule over the class (`linarith` already works at
   any `OrderedField + CommRingOfInt`).

Whether evidence rules about a class-generic predicate can be registered
once and fire at each instance's carrier is the open question for (2).
