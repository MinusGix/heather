---
title: TwoProduct by fma
status: closed
labels: [mathematics, floating-point]
area: mathematics
milestone: [float-eft, math-float]
created: 2026-10-31
updated: 2026-11-01
---

`p = ○(a·b)`, `e = ○(fma(a, b, -p))` gives `p + e = a·b` in a nearest mode
when the product does not underflow (design §19).

## What it assumes from elsewhere

- **[[float-eft-sterbenz-fast2sum]]** owns `rep_on_grid` and `nbr_grid`.
  Assumed here: they apply at the product's grid.

## Notes

`a·b` is on the grid `2^(qa + qb)` and `|a·b - p| <= ulp(p)/2`, so the
error has at most `prec` significant bits; it is a float when its exponent
is at least `qmin`, which is the hypothesis `qa + qb >= qmin` (equivalently
the exact product is not below the subnormal grid). In half-units the
product's grid is not a float's own grid, so `OnGrid` needs a form at an
arbitrary exponent, or the proof shifts by `qa + qb - qmin`. The fma step
is then `exact_of_rounds` at `Finite::fma_correct`. A negative control: an
underflowing product whose error is not a float.

## Resolution (2026-11-01)

Proved as `Finite::two_product` and `Finite::two_product_exact` in
`lib/std/num/float/eft.hthr` (design §19). The no-underflow hypothesis is
`a.q() + b.q() = F.qmin() + c` for a natural `c`, plus `|a·b| <= max`. The
arbitrary-exponent grid became `Format::rep_fit` (fewer than `top` cells of
`2^(c+1)` half-units is a float), so `OnGrid` needed no new form. The
negative control is `tp_needs_grid`: `(1025 · 2^-22)²` at binary16.
