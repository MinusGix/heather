---
title: "Research differential-valued fields and grid-based transseries"
status: open
labels: [mathematics,analysis,research,design]
area: mathematics
created: 2026-10-27
updated: 2026-10-27
---

Layer G and the meeting point of `docs/analysis-foundations-design.md`
(§3.3, §11): research, not scheduled. Differential-valued fields
(Rosenlicht), H-fields and newtonian fields (Aschenbrenner–van den
Dries–van der Hoeven), with grid-based transseries as the main instance.

Questions to settle when it is picked up:

- the class over the two axes ([[differential-structures]]'s derivation and
  [[valued-rings-and-newton]]'s dominance) with Rosenlicht's compatibility,
  first inhabited by Laurent series in `x` with `d/dx`;
- representation of a grid-based support and the finite factorisation lists
  that replace `antidiag` in convolution; coinduction over a well-based order;
- witnessed positivity (leading monomial and a positive coefficient as data),
  the constructive order, and what normalising requires (zero tests are
  undecidable for infinite streams even over `Rat`);
- the tower in steps: Laurent (`ℤ`), Puiseux (`ℚ`), `x^a log^b x`, then
  exponentials, each an object with a customer of its own;
- a certifying Gruntz algorithm for limits of exp-log expressions;
- which results of van der Hoeven (2006) and ADH (2017) are in reach
  constructively, including the differential Newton lemma for ODE
  perturbation.

## What it assumes from elsewhere
- **[[formal-power-series]]**: the ℕ case and the `antidiag` hook.
- **[[regular-perturbation-expansions]]**: the algebraic perturbation customer.
