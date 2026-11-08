---
title: Close the class-carrier division gaps: written sign goals, numerals, trace spelling
status: open
labels: [mathematics,tactics,diagnostics]
area: mathematics
milestone: [math-classes]
created: 2026-11-06
updated: 2026-11-08
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

## Log

- 2026-11-08: Stdlib awkwardness survey (docs/stdlib-math-awkwardness-survey.md §2): the numerals bullet is the largest single cost in the generic analysis files (`K.unit` 353, `.multiplicative.unit` 656, `K.inv(` 489 in lib/std); it moves to [[class-carrier-arithmetic-surface]] together with prefix/infix `-` and linarith reading `e / 2` at a class carrier (refused today, proved at `Rat`). This issue keeps the written-sign-goal and trace-spelling bullets.
