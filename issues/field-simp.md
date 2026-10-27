---
title: Clear denominators before ring at fields (field_simp)
status: open
labels: [tactics,arith,reals]
area: tactics
milestone: [tac-arith]
created: 2026-10-27
updated: 2026-10-27
---

`ring` normalises commutative-ring expressions, but at `Rat` its atoms
include the denominators. A goal with any division or `inv_succ`, and even
plain sums of abstract rationals at `≈`, fails unless the user passes `den`
facts by refl (`Rat::scale_inv_succ` passes four). So identities like
`x·(1/2) + x·(1/2) ≈ x` are proved by hand from `mul_add_distr`,
`inv_succ_half` and `mul_one`.

Wanted: a `field_simp` step before `ring`, at any field and at `≈`.

Scope:

- move every `recip` / `inv` / `Rat(1, d)` to a common denominator, and
  prove the cleared equation equivalent to the original one through the
  field laws (`OrderedField::recip_unique`, `mul_recip`);
- side conditions (each denominator apart from zero) are discharged from
  `Pos` binders, numerals and hypotheses, or reported as open;
- then `ring` decides the cleared identity at the ring's `≈`, without
  unfolding `Rat`'s representation, so the same proof works at `CReal` given
  apartness facts;
- the inequality form (positive denominators preserve `<=`) feeds
  `linarith-ordered-fields`.

## What it assumes from elsewhere
- **[[linarith-ordered-fields]]**: the consumer of the cleared inequalities.
- **[[ring-inequalities]]**: the normaliser it hands off to.
