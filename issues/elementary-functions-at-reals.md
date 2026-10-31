---
title: exp, sin, cos at real arguments, and their laws
status: open
labels: [reals]
area: mathematics
created: 2026-10-27
updated: 2026-10-31
---

`CReal::exp_rat`, `sin_rat`, `cos_rat` (`lib/std/num/float/elementary.hthr`)
are defined at rational arguments only, and none of their laws is proved:
the probes show `sin(1)² + cos(1)² < 1.001` by enclosures, not `≈ 1`.

Scope:

- the functions at a real argument: either the series with real terms
  (a `CReal` version of `Series`, whose limit is `CReal::lim`), or the
  rational function extended by a modulus of continuity on bounded sets;
  the second keeps the enclosures as they are, read at an enclosure of the
  argument;
- the laws: `exp(a + b) ≈ exp(a) · exp(b)` (Cauchy product of the two
  series, or uniqueness of the solution of `f' = f` once
  `real-functions-and-derivatives` lands), `sin² + cos² ≈ 1`, the addition
  formulas, monotonicity of `exp`;
- an `Enclosed` leaf at real arguments, so `by intervals()` reads
  `exp(x)` for any real `x` it can enclose.

## What it assumes from elsewhere
- **[[interval-elementary-functions]]** (closed) owns the rational case.
- **[[real-functions-and-derivatives]]** owns continuity and derivatives at
  `CReal`, which one route to the laws goes through.

## Log

- 2026-10-27: docs/analysis-foundations-design.md §8 proposes the laws as formal identities proved by coinduction over Hurwitz series ([[formal-power-series]], §3.4) carried through evaluation as a ring homomorphism ([[power-series-evaluation]]); no real derivatives needed.
- 2026-10-31: 2026-10-31: `CReal::log_rat` exists (lib/std/num/float/elementary.hthr, the atanh series after scaling into one binade, plus e·log 2), defined as that sum: `exp(log q) ≈ q` and `log(exp a) ≈ a` are owed here with the other laws ([[creal-compress-and-transcendentals]]).
- 2026-10-31: exp-log-grid-gap closed for exp (2026-10-31, lib/std/num/float/pade.hthr). log's gap is now [[log-grid-gap]], blocked here: it needs exp(log q) ≈ q and exp monotone or Lipschitz on a bounded interval at real arguments.
