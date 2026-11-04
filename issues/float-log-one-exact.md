---
title: log(1) = +0 exactly, in every mode
status: closed
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

## Resolution (2026-10-31)

`Format::log_pos` (transcendental.hthr) answers `a.val() ≈ 1` (decided by
`Rat::same_dec`, new in rat.hthr) with `+0` before the search; `Float::log`
calls it on positive arguments. `CReal::log_rat_of_one` (elementary.hthr)
proves `log_rat(q) ≈ 0` at every spelling of 1: `num = den`, so the binade
is `Binade::of(n, n)`, whose ends agree and whose exponent is 0
(`Binade::of_diag`); the atanh series at equal ends is exactly 0
(`Series::atanh2_diag`) and the ln 2 term is scaled away (`Binade::log_zero`).
`Float::log_one` states `log(1) = +0` in every mode, for any tries.

One premise above was wrong: at binary32 the search alone does end at 1 in
every mode, and lands on `+0`, because the enclosure it builds is exactly
`[0, 0]` (first term 0, exponent 0); a probe records it. Answering first
still matters: nothing in the search's theorem fixes the zero's sign, and
the answer no longer depends on how the enclosure is built.
