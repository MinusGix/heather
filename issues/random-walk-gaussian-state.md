---
title: Random-walk states converge to the Gaussian state on polynomials
status: open
labels: [mathematics,probability,continuous-time]
area: mathematics
milestone: [ml-gaussian-states]
created: 2026-11-10
updated: 2026-11-10
---

Brownian motion at time `t` as the limit of its step program, stated
without measure theory: the states of the symmetric random walk with step
`√dt` converge, on every polynomial, to the centred Gaussian state of
variance `t` (`docs/continuous-time-survey.md` §5.3).

This is the headline example of Imada and Hsu (arXiv 2611.12761, Program 1:
`E[xⁿ] = (n - 1)!!` for even `n` in the limit), restated so that the limit
is a state on a polynomial algebra and not a measure, and carries a rate:
the gap on each monomial is `O(dt)`. Probes at `Rat` for the first, second
and fourth moments, with the exact discrete values:
`lib/_tests/std/analysis/continuous_time_tests.hthr` (`walk_mean`,
`walk_second`, `walk_fourth`, `walk_unit_fourth_continuous`).

Scope:

- the walk's `n`-step state as a finitely supported distribution's
  expectation, and its moments by the binomial recurrence;
- convergence of every moment to the Gaussian state's, with the linear
  rate;
- drift and scaled steps (`x += μ·dt + σ·db`) as the affine image.

Not in scope: that the Gaussian state is integration against a measure,
Wasserstein or weak convergence, stopping times, reflected or absorbed
walks. Those need measure theory or the guard question
(`docs/continuous-time-survey.md` §5.4).

## What it assumes from elsewhere

- **[[finite-probability]]** owns finitely supported distributions and
  expectation as a state. Assumed here: that interface.
- **[[ml-gaussian-states]]** owns the Gaussian state and Wick's rule.
  Assumed here: its moments on monomials.

## Log
