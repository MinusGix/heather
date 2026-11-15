---
title: Sterbenz, the nearest addition error and Fast2Sum
status: closed
labels: [mathematics, floating-point]
area: mathematics
milestone: [float-eft, math-float]
created: 2026-10-31
updated: 2026-10-31
---

The first part of `float-eft` (`docs/library/floating-point-design.md` §8 round 5,
§19): the error-free transformations that need nothing but the grid.

Landed in `lib/std/num/float/eft.hthr`:

- **Representability.** `Format::rep_below`: a natural multiple of
  `2^(g.bexp + 1)` half-units no larger than a float `g` is a float (the
  greatest float at or below it is exactly it). `Format::rep_on_grid` is the
  signed form over `OnGrid(c, z)` (`z = ±n·2^(c+1)`).
- **Exact results.** `Float::Exact(o, v)` says `o` is the finite float of
  value `v`; `Format::exact_of_rounds` gives it in every mode once `v` is a
  float.
- **Sterbenz.** `Finite::sterbenz`: for `y ≤ 2x` and `x ≤ 2y`, `x - y` is
  exact in every mode, subnormals included and with no overflow hypothesis.
- **Grid preservation.** `Format::nbr_grid`: either neighbour of a value on
  a float's grid is on that grid, so no correct rounding leaves it.
- **The nearest addition error.** `Finite::add_error`: for `s` the nearest
  rounding of `a + b`, `(a + b) - s` is a float. It is false for the
  directed modes (`err_up_not_float` in the tests).
- **Fast2Sum.** `Finite::fast_two_sum` (`s - a` exact for `|b| ≤ |a|`),
  `fast_two_sum_err` (`b - z` is the error, exactly) and
  `fast_two_sum_exact` (`s + t = a + b`). The two subtractions may use any
  mode; only `s` must be a nearest rounding. The only hypothesis besides
  `|b| ≤ |a|` is that `s` is finite: doubling `a` past the largest float is
  handled, not assumed away.

The remaining parts of the milestone are [[float-eft-two-sum]],
[[float-eft-two-product]], [[float-eft-veltkamp]] and
[[float-kahan-summation]].
