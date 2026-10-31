---
title: Put log at floats off the rounding grid, read through exp's Padé gap
status: blocked
labels: [mathematics,reals,float]
area: mathematics
milestone: [float-transcendental]
blocked-by: [elementary-functions-at-reals]
created: 2026-10-31
updated: 2026-10-31
---

exp's gap is done (`Format::exp_off_grid`, lib/std/num/float/pade.hthr).
log's is the same bound read through exp, as flean's `LogTermination.lean`
does. It needs a law the library does not have: `CReal::log_rat` is defined
as the atanh sum, and `exp(log q) ≈ q` is owed in
[[elementary-functions-at-reals]].

The argument, once that law exists:

- `Format::off_grid_of_apart` reads apartness only at the two ends `g`,
  `g'` of the cell holding a rational approximation of the real. So a
  per-point apartness is enough. There is no need for one distance over the
  whole grid.
- For a grid point `g ≠ 0`, `CReal::exp_apart_lattice(g)` puts `exp(g)` a
  fixed distance from every point of the lattice `2^-d Z`, and so from `q`,
  a float value. If `log q` were within `ε` of `g`, then `q = exp(log q)`
  would be within `exp(|g| + 1)·ε` of `exp(g)`. That needs exp to be
  monotone, or Lipschitz on a bounded interval, at `CReal` arguments,
  which is also owed in [[elementary-functions-at-reals]].
- `g = 0` is `q = 1`, log's exact case
  ([[float-log-one-exact]]), answered before the search.
- The log boxes need narrowing as exp's do ([[exp-box-narrowing]]), or the
  total version searches over `CReal::enclosed`, as `Float::exp_total`
  does.

## What it assumes from elsewhere
- **[[elementary-functions-at-reals]]** owns `exp(log q) ≈ q`, and exp at
  real arguments with its monotonicity.

## Log

- 2026-10-31: exp at real arguments is monotone and Lipschitz on bounded sets now (`CReal::exp_le`, `CReal::exp_lt`, `CReal::exp_dev`, lib/std/num/float/elementary_real.hthr), so the second bullet's half is done. Still blocked on `exp(log q) ≈ q`: [[elementary-functions-at-reals]] says why it is not cheap.
