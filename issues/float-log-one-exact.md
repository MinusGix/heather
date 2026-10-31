---
title: log(1) = +0 exactly, in every mode
status: open
labels: [mathematics,float]
area: mathematics
milestone: [float-transcendental]
created: 2026-10-31
updated: 2026-10-31
---

`Float::log` (lib/std/num/float/transcendental.hthr) sends every positive
finite argument to Ziv's search. At 1 the real is the rational 0, a
breakpoint in every directed mode: every enclosure of 0 straddles it, so
`TowardNeg` sees `-min_subnormal` at one end and `+0` at the other and the
search returns `None` whatever its tries. In the nearest modes it ends, but
`round_box` may hand back `-0`, where IEEE 754 §9.2 fixes `+0`.

`Float::exp` already does this for its one rational value, exp(±0) = 1, by
answering it before the search (`CReal::exp_rat_of_zero`, `Float::exp_correct`'s
zero arm).

Scope: decide `a.val() ≈ 1` for a finite `a` (a positive sign, `mag` the
format's `half`, `q = -frac`), answer `Fin(Finite::zero(F, False))`, and
prove `CReal::log_rat(q, pos) ≈ 0` at `q ≈ 1`: `num.natAbs = den`, so
`Binade::of(n, n)` is `(n, n, 0)` in either arm of its width test, the
atanh series has first term and every ratio's product 0, and the ln 2 term is
scaled by 0.
