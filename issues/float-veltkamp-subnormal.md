---
title: Veltkamp splitting at a subnormal input
status: open
labels: [mathematics, floating-point]
area: mathematics
milestone: [math-float]
created: 2026-11-01
updated: 2026-11-01
---

`Finite::veltkamp` (design §19) assumes `x` normal (`half <= x.mag`). The
split still holds for a subnormal `x` with `xh` and `xl` on the grids the
statement names, but the proof's first step, `C·x >= half·2^(c+s+1)` so
that `g`'s exponent is at least `c + s`, fails: a subnormal's significand
is below `half`.

## What it assumes from elsewhere

- **[[float-eft-veltkamp]]** (closed) owns the normal case and its lemmas
  (`vk_*` in `lib/std/num/float/eft.hthr`).

## Notes

The likely route reads `x` at its own leading bit rather than at `bexp`
(a subnormal `m·2^1` is a normal number of a wider exponent range), or
splits on whether `C·x` is itself subnormal: then `g = C·x` exactly when
it fits, and `d = x - g = -S·x`, `xh = x` and `xl = 0` might follow by
direct computation. Low priority: Dekker's product, the customer, already
excludes underflow.

## Log

- 2026-11-05: gardener: cites a file it shares with [[match-on-proof-call-cost]] (`lib/std/num/float/eft.hthr`).
