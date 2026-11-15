---
title: Solve a Lipschitz ODE as the limit of Euler's method
status: open
labels: [stdlib,mathematics,analysis,reals,continuous-time]
area: mathematics
milestone: [math-reals]
created: 2026-11-10
updated: 2026-11-10
---

Solutions of `x' = f(t, x)`, `x(0) = x₀` for a Lipschitz field as the limit
of Euler's step program, so that an ODE solution is a term that computes
(`docs/surveys/continuous-time-survey.md` §5.2 item 3).

Scope, scalar first, at a `CauchyComplete` ordered field:

- the Euler program as a function of the resolution;
- a discrete Grönwall inequality (`eₙ₊₁ <= (1 + L·dt)·eₙ + c·dt²` gives a
  bound uniform in `n·dt <= T`);
- the Euler family is Cauchy in the step with an explicit modulus, of
  order 1; its limit `solve(f, x₀, T)`;
- the limit satisfies the integral equation and is the only function that
  does (uniqueness by the same Grönwall bound).

Acceptance probe: the Euler program for `x' = x` has limit `CReal::exp`.

Picard iteration (Makarov and Spitters did it in Coq over CoRN) is the
alternative; it needs function spaces as complete spaces, where
`Contraction::fixed_point` is stated for points of the field only. Euler
with Grönwall needs neither and matches the step-program reading, so it
goes first.

Not in scope: systems (vector state), guards and events
(`docs/surveys/continuous-time-survey.md` §5.4), higher-order methods.

## What it assumes from elsewhere

- **[[riemann-integration]]** owns the integral. Assumed here: the integral
  of a uniformly continuous function and its bound.
- **[[step-families-and-order]]** owns the order record. Assumed here: its
  definition.

## Log
