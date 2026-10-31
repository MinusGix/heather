---
title: State float operations, the square root and the error model at the reals
status: closed
labels: [mathematics,reals,float]
area: mathematics
milestone: [float-reals]
created: 2026-10-31
updated: 2026-10-31
---

The first part of `float-reals` (docs/floating-point-design.md §6, §17).
[[float-sqrt]] stated the root's value theorem at every rational in `√x`'s
cell and left two things for the reals: that the real `√x` itself is
rounded, and the standard model `|r - √x| ≤ u·√x`, which needs `√x` as a
value. [[creal-compress-and-transcendentals]] had added `RoundsToReal`.

## Done when

- A float's real (`Finite::real`) and the operations with rational exact
  values at the reals, from the `Rat` theorems.
- A real square root of a rational, with a characterisation every
  comparison reads, and `RoundsToReal(F, mode, √x, a.sqrt())`.
- The error model (with underflow, and relative in the normal range) at
  reals, and the root's.
- Probes at binary16 literals, with a negative control.

## Resolution (2026-10-31)

`lib/std/num/float/float_real.hthr`, design §17. `CReal::IsSqrt(s, x)` is
the root as a cut (`is_sqrt_of_sq` from `s * s ≈ x`); `CReal::sqrt_rat(q)`
is `√|q|` from `Rat::root_floor` (integer root of `⌊|q|·4^n⌋` by `ldiv` and
`isqrt`, terms evaluate), with `sqrt_rat_is_sqrt`. `Finite::sqrt_real` and
`sqrt_rounds_real` are the value theorem; the interval is the exact grid
point, or rationals strictly inside the cell from `Rat::root_above` and
`root_below`. `Format::real_error_nonneg` and `real_relative_nonneg` carry
the error model to nonnegative reals by cutting the rounding interval into
range and reading the affine bound at both ends (`CReal::err_between`);
`Finite::sqrt_real_error` and `sqrt_real_relative` are the root's.

What is left of the submilestone is [[float-reals-next]] and
[[float-round-real-termination]].
