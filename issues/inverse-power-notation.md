---
title: Inverse and power notation without junk values
status: open
labels: [stdlib,mathematics,reals,syntax]
area: mathematics
created: 2026-10-18
updated: 2026-11-06
---

Write `x⁻¹` and `x ^ n` the way Lean does, with `x ^ (-1)` agreeing with
`x⁻¹`, but keep the hypothesis instead of a junk `0⁻¹ = 0`. Design:
docs/library/inverse-power-notation-design.md.

## Done in this round

- Postfix `⁻¹` and right-associative `^` (above prefix `-`, below postfix),
  `designation postfix`, formatter and editor grammar.
- `Rat`: `Apart`, sign predicates and rules, `inv` at `x.Apart(0) := infer`
  (the total reciprocal is now `recip`), `npow`, `PowOk`, `pow`,
  `pow_neg_one`, `pow_negSucc_inv`; rules for products, inverses, powers.
- `CReal`: `⁻¹` on the existing inverse, sign rules, `ofRat_apart`,
  `ofRat_inv`, `npow`, `pow`, `pow_neg_one`.
- Search: a goal whose relation has no rules is unfolded to one that has;
  written-out pairs and sums have prefilter heads.

## Left

- Integer-exponent laws: `pow_add` over `Int`, `(x * y) ^ n`, `(x ^ m) ^ n`.
- State `inv`/`pow` once in [[constructive-ordered-field-interface]].

## Log

- 2026-10-19: `inv` is now stated once ([[constructive-ordered-field-interface]]: `OrderedField.inv` at apartness, `inv_unique`/`inv_respects` generic). A generic `pow` is not; it stays here.
- 2026-11-06: The division round (docs/library/division-design.md) closed two of the leftovers: `apart_of_nonzero` is a rule over a one-place `x.Nonzero()`, so a local `¬(x ≈ 0)` gives `x⁻¹` at `Rat`, and `CReal` has `apart_mul`, `apart_inv`, `apart_div`. Integer-exponent laws remain.
