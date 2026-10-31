---
title: IEEE exp and log on every float, specials included
status: closed
labels: [mathematics,float]
area: mathematics
milestone: [float-transcendental]
created: 2026-10-31
updated: 2026-10-31
---

`Format::exp_fin` and `Format::log_fin` (lib/std/num/float/transcendental.hthr)
take a finite float, and `log_fin` a proof that it is positive. IEEE 754
§9.2 also fixes `exp(+∞) = +∞`, `exp(-∞) = +0`, `log(±0) = -∞` (divide by
zero), `log(x < 0) = NaN` (invalid) and `log(+∞) = +∞`, NaN in NaN out, and
formats without infinities or NaN (`Specials`) need their own reading, as
`Float::div` already has.

Scope: `Float::exp` and `Float::log` over `Float(F)` with those cases,
deciding the sign of a finite argument, and a correctness theorem that is
`RoundsToReal` at a finite result and the special value otherwise. Overflow
needs nothing new: a real past the overflow threshold rounds to infinity
through the same search, since both ends of its enclosure do.

## What it assumes from elsewhere
- **[[exp-log-grid-gap]]** owns whether a finite argument
  always gets `Some`. Assumed here: nothing; the wrapper passes `None` on.

## Done (2026-10-31)

`Float::exp` and `Float::log` in lib/std/num/float/transcendental.hthr, with
`Finite::sign_dec` (zero, positive or negative, with the evidence) in
arith.hthr. Theorems: `Float::exp_correct` and `Float::log_correct`
(`RoundsToReal` at a finite argument; log's read at any positivity proof
through `CReal::log_rat_irrel`, which holds term by term), and the special
values `exp_inf`, `exp_neg_inf`, `exp_nan`, `exp_zero`, `log_zero`,
`log_zero_inf`, `log_neg`, `log_inf`, `log_neg_inf`, `log_nan`.

One case beyond the scope above: exp(±0) = 1 is answered before the search
(`CReal::exp_rat_of_zero`), since every enclosure of 1 straddles a directed
mode's breakpoint and the search would return `None`. log(1) = +0 has the
same shape and is [[float-log-one-exact]]. Overflow is the search, as
expected: `exp_four_e3m2` saturates at a format without infinities.
