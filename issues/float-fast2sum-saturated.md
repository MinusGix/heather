---
title: Fast2Sum's exact overflow error under saturation
status: open
labels: [mathematics,floating-point]
area: mathematics
milestone: [math-float,p3109-projection]
created: 2026-11-25
updated: 2026-11-25
---

FLoPS (§4, Theorem 12) proves that under saturation Fast2Sum computes the
overflow error exactly: for finite `a`, `b` with `|a + b|` past the largest
finite value `M`, `e_a >= e_b`, and `s` saturated (`|s| = M`), `t = (a + b)
- s` exactly, *whatever mode rounded `s`*.

## Where the library already is

`Finite::fast_two_sum` (`lib/std/num/float/eft.hthr`) takes `s` as a
nearest rounding of `a + b` and assumes nothing about overflow beyond `s`
being finite (design §19). `Finite::Nearest` only says no float is closer,
and in a format without infinities a nearest rounding past the range is
the largest float. So for E4M3, E3M2, E2M3 and E2M1 the theorem should
already cover the overflow case when `s` is rounded to nearest. Check that
with two evaluation tests in `lib/_tests/std/num/float/eft_tests.hthr`:
E4M3 with `a + b` past 448, and E2M1 with `a + b` past 6.

## What is new

`s` rounded in a directed mode and saturated. With
[[float-saturation-modes]] that also covers a format with infinities under
`SatFinite`. A likely route: a saturated `s` is a faithful rounding, so
`s - a` should be exact by the Sterbenz argument the nearest case uses,
and `b - z` is then `(a + b) - s`; whether that error is a float is the
part to prove (FLoPS §4 has the argument). FLoPS also needed the middle
step's overflow immunity at precisions one and two (their Theorem 11),
since Boldo et al.'s proof assumes at least three bits; the library's
proof never went through that bound, so only precision one
([[float-precision-one]]) is new there.

## What it assumes from elsewhere

- **[[float-saturation-modes]]** owns saturation as a parameter. Assumed
  here: only that a saturated result is a faithful rounding.

## Log

- 2026-11-25: The nearest-mode half is confirmed by evaluation: `lib/_tests/std/num/float/eft_tests.hthr` runs `Finite::fast_two_sum_exact` at E4M3 (416 + 64 saturates to 448, error 32) and E2M1 (4 + 4 saturates to 6, error 2). The directed-`s` theorem is still open; it wants [[float-saturation-modes]] for the format-with-infinities case.
