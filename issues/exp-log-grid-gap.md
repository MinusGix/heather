---
title: Prove exp and log at floats clear of the rounding grid (Padé gap) and their enclosures narrow
status: open
labels: [mathematics,reals,float]
area: mathematics
milestone: [float-transcendental]
created: 2026-10-31
updated: 2026-10-31
---

`Format::round_real_apart(mode, e, narrow, off)` (lib/std/num/float/round_real.hthr)
is Ziv's search with no `Option`. It asks for two proofs about the real
`e.x`, and for `exp` and `log` neither exists yet:

- **`off: F.OffGrid(e.x)`**, a half-unit grid cell holding the real `2^-k`
  clear of both ends. For `exp(x)` at a dyadic `x ≠ 0` this is the Padé
  bound: flean's `ExpEffectiveBound.lean` / `ExpTermination.lean` bound
  `|exp(x)·2^s - m|` away from zero, which is the cell statement with
  `s = 1 - qmin`. `exp(0) = 1` is a grid point and takes its own (exact)
  case. For `log(q)` at a positive rational `q ≠ 1`, the same bound read
  through exp (flean's `LogTermination.lean`), and `log(1) = 0` exactly.
- **`narrow: e.Narrows(n, p, 16)`** for `CReal::exp_box` and
  `CReal::log_box`: every width is reached at some try. The series boxes
  narrow in both the term count and the precision; nothing proves it yet.
  `Enclosed::narrows_of` reduces it to "narrower than `2^-k` from some index
  on, at any precision", which is how `CReal::enclosed_narrows` was proved.

With both, `Format::exp_fin_total(mode, f)` is `round_real_apart` over
`exp_box` and carries `RoundsToReal` with no `Option` and no tries.

Size: flean's Padé side is about 4,000 lines of Lean over Mathlib
(`PadeExp*.lean`, `IrrationalExp.lean`, `ExpEffectiveBound.lean`, the two
`*Termination.lean`), leaning on Mathlib's integrals and Taylor remainders.
Heather has neither at `CReal`, so the remainder estimate is the first thing
to design: either the integral form over a new Riemann sum, or the explicit
Padé polynomials `P_n`, `Q_n` with the remainder bounded term by term from
the series (no integral), which is the more likely fit.

## What it assumes from elsewhere
- **[[float-round-real-termination]]** (closed) owns the search's end:
  assumed here only the two hypotheses of `round_real_apart` as stated.
- **[[elementary-functions-at-reals]]** owns exp's laws at `CReal`; the
  Padé identity needs at most the series and `exp(a)·exp(b)`, if that.
