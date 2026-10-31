---
title: IEEE exp and log on every float, specials included
status: open
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
