---
title: State division once over the ordered-field classes
status: closed
labels: [stdlib,mathematics,notation]
area: mathematics
milestone: [math-classes]
created: 2026-11-06
updated: 2026-11-06
---

`/` and `⁻¹` are designated at `Rat` and `CReal` with a searched
apartness (docs/library/division-design.md), each carrier restating the same
definitions, laws and sign rules. The generic classes have
`OrderedField::recip(x, h)` but no symbol, so a section over
`A: OrderedField(…)` writes `x * A.recip(x, h)` and passes `h` by hand.

Wanted, in order:

1. `⁻¹` and `/` inside a section over an ordered field, at the
   dictionary's `recip` with `h: ApartBy(<, x, A.unit) := infer` (needs a
   designation, or a binder symbol, for a postfix operator and a defaulted
   proof at a class carrier; docs/language/classes/operators-onto-classes-design.md).
2. The division laws (`div_mul_cancel`, `div_respects`, `add_div`, …)
   and the sign rules stated once there, with `Rat`/`CReal` reading them
   through the instance; the carrier copies then go.
3. The `nlinarith` search rule over the class (`linarith` already works at
   any `OrderedField + CommRingOfInt`).

Whether evidence rules about a class-generic predicate can be registered
once and fire at each instance's carrier is the open question for (2).

## Log

- 2026-11-06: Done (Minus asked for it 2026-11-06). lib/std/algebra/field_division.hthr:
  `OrderedField::Invertible`, `inv`, `div`, and `designation postfix ⁻¹ at
  OrderedField` / `designation / at OrderedField`, which a section's operand at
  its type parameter reads through the dictionary in scope (operator ladder rung
  2b). The laws (div_mul_cancel, mul_div_cancel, div_self, one_div, zero_div,
  div_respects, add_div, sub_div, neg_div, mul_div_assoc, inv_mul_distrib,
  div_mul_div, inv_inv, inv_any_proof, div_any_proof) and the sign rules, over
  sign predicates generic in the relation (`PositiveBy(<, <=, zero, x)`, so a
  sign premise is smaller than `Invertible`). The open question had a yes:
  evidence rules stated in a class section register once and fire at the
  section's carrier, after two elaborator changes (a dictionary premise is
  exempt from the Paterson check; a first-order pre-match skips a rule whose
  operation binder would meet another operation). `nlinarith` search rules
  work since tactic defaults keep a class carrier's dictionary; `ring` and
  `linarith` read the class's `/` and `⁻¹`. Rules are stated at `OrderedField`,
  not the weakest class: a weaker class's rule built a parent record per
  application, about twenty times the cost. The carrier copies stay for now:
  [[carrier-division-through-class]]. Gaps: [[class-carrier-division-gaps]],
  [[ring-reciprocal-of-searched-proof]].
