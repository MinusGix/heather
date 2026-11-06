---
title: Close the class-carrier division gaps: written sign goals, numerals, trace spelling
status: open
labels: [mathematics,tactics,diagnostics]
area: mathematics
milestone: [math-classes]
created: 2026-11-06
updated: 2026-11-06
---

Inside `section<K: OrderedField(≈, <, <=, +, *)>` a divisor's apartness is
searched through the sign predicates `PositiveBy`, `NegativeBy`, `NonNegBy`
(lib/std/algebra/field_division.hthr). Three gaps against `Rat`:

- **A sign goal written with `<`.** `h: K.unit < e := infer` (or a
  `positivity`-style goal) has the section's `<` for a head, a local, and no
  evidence rule can be keyed on a local relation (`proposition_key` wants a
  global). `Rat` has `lt_of_positive`; here the goal has to be written
  `PositiveBy(<, <=, K.unit, e)`. Either key rules on a class index (the
  relation's slot in the dictionary's class) or rewrite a `<`-headed goal at a
  class carrier to the predicate before searching.
- **No numerals at a class carrier.** `a / 2` needs `Ring::int_cast<K>(OfNat(2))`
  spelled out, and there is no rule giving it a sign
  (`OrderedField::of_nat_pos` exists, as a theorem).
- **The search trace spells the section's hidden binders**:
  `no instance for Invertible(#constraint0.unit)` for `a / K.unit`, as
  linarith's goal display did before issues/class-carrier-diagnostics-spell-placeholders.md.
