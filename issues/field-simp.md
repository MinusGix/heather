---
title: Clear denominators before ring at fields (field_simp)
status: closed
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

## Log

- 2026-10-27: Done for equations (docs/tactics/ring-normalization-design.md §9). It is
  not a separate step: at a `≈` carrier with `CommRingOfInt` (`Rat`, `CReal`)
  `ring` reads `x⁻¹` and `Rat::inv_succ(n)` as atoms with the facts that clear
  them (`<op>_mul`: `x⁻¹ * x ≈ 1`, `Rat::inv_succ_cancel`), and casts of `Nat`
  sums, products and successors with `RingExpr::of_nat_add` and its kin. The
  facts' multipliers are computed by eliminating the reciprocals one at a
  time, so a true field identity is never missed. Side conditions are the
  apartness `x⁻¹` was elaborated with; nothing more is owed. Five `CReal`
  calc chains became `ring` steps; probes in
  `lib/_tests/std/tactic/ring_field_tests.hthr`.
  Not done, and where it went: the inequality form is
  [[linarith-ordered-fields]]'s (noted there); generic `A.recip` and total
  `Rat::recip` stay atoms (§9 "Not in this round"); a field read like
  `x.seq(n)` refuses the reading, [[ring-field-read-atom-spelling]].
