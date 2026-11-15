---
title: Integrate uniformly continuous functions as the limit of Riemann sums
status: open
labels: [stdlib,mathematics,analysis,reals,continuous-time]
area: mathematics
milestone: [math-reals]
created: 2026-11-10
updated: 2026-11-10
---

The integral of a uniformly continuous function on `[a, b]` as the limit of
the step program `x += f(t)·dt` (`docs/surveys/continuous-time-survey.md` §5.2 item
2). `math-reals` has no integration yet, and ODE solutions, expectations
against a density and the fundamental theorem all wait on it.

Scope, at a `CauchyComplete` ordered field:

- the left Riemann sum on the uniform partition as a function of the
  resolution, Cauchy with a modulus computed from `f`'s modulus of uniform
  continuity; the integral is its limit;
- linearity, monotonicity, the bound `|∫f| <= M·(b - a)`, additivity over
  adjacent intervals;
- the fundamental theorem against `DerivOn`, in both directions;
- for Lipschitz `f` the order: the sum at step `dt` is within
  `L·(b - a)·dt/2` of the integral ([[step-families-and-order]]).

Acceptance probe: `∫₀ᵀ 2t dt ≈ T²` from the theorems, and the same value
read off a run by Richardson.

## What it assumes from elsewhere

- **[[real-functions-and-derivatives]]** owns `UnifContOn`, `LipschitzOn`
  and `DerivOn`. Assumed here: their definitions and the mean value
  inequality.
- **[[real-completeness-interfaces]]** owns `CauchyComplete`. Assumed here:
  that a Cauchy sequence with a modulus has a limit.

## Log
