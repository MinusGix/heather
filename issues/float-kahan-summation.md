---
title: Kahan's compensated summation error bound
status: closed
labels: [mathematics, floating-point]
area: mathematics
milestone: [float-eft, math-float]
created: 2026-10-31
updated: 2026-11-01
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

## Resolution (2026-11-01)

Scoped to the warm-up and the step (Minus picked the scope with the round).
In `lib/std/num/float/summation.hthr` (design §19), probes in
`lib/_tests/std/num/float/summation_tests.hthr`:

- `Finite::add_rel_error`: addition's standard model with no underflow
  term (a sum below the least normal is exact), in every mode.
- `Format::rec_sum_error`: the recursive sum of `n + 1` floats, every exact
  partial sum in range, is within `γ(n)·∑|xᵢ|`, in every mode.
- `Finite::kahan_step`: Kahan's correction is exact and `t - c = s + y`
  when `|y| <= |s|` and `t` rounds to nearest.

The whole-loop bound `(2u + O(n·u²))·∑|xᵢ|` and Neumaier's variant are
[float-kahan-bound](float-kahan-bound.md).
