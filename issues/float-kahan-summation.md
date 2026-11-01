---
title: Kahan's compensated summation error bound
status: open
labels: [mathematics, floating-point]
area: mathematics
milestone: [float-eft, math-float]
created: 2026-10-31
updated: 2026-10-31
---

Kahan's compensated summation over a list of floats has error at most
`(2u + O(n·u²))·∑|xᵢ|` (Higham, Theorem 4.8), against the recursive sum's
`γ(n-1)·∑|xᵢ|` (design §19). Neumaier's variant (the branch on `|s| ≥ |x|`)
is the same proof with Fast2Sum in both orders.

## What it assumes from elsewhere

- **[[float-eft-sterbenz-fast2sum]]** owns Fast2Sum. Assumed here: each
  step's correction is exact when Fast2Sum's ordering holds.
- **`float-error`** (`lib/std/num/float/error.hthr`) owns the standard model
  and γ. Assumed here: `gamma_prod` and `standard_model` compose over a list.

## Notes

Kahan's correction step is a Fast2Sum only when `|s| >= |y|`, which the
algorithm does not ensure; Higham's proof works through the standard model
instead and is a γ-composition over the list. The recursive sum's own bound
(`γ(n-1)`) is the warm-up and is not proved yet either; it belongs here as
the comparison.
