---
title: Research grid-based transseries over a constructive base
status: open
labels: [mathematics,analysis,research,design]
area: mathematics
created: 2026-10-27
updated: 2026-10-27
---

Layer G of `docs/analysis-foundations-design.md` (§10): research, not
scheduled. Transseries as generalised power series over an ordered monomial
group with grid-based supports.

Questions to settle when it is picked up:

- representation of a grid-based support and the finite factorisation lists
  that replace `antidiag` in convolution;
- witnessed positivity (leading monomial and a positive coefficient as data),
  the constructive order, and what normalising requires (zero tests are
  undecidable for infinite streams even over `Rat`);
- the tower in steps: Laurent (`ℤ`), Puiseux (`ℚ`), `x^a log^b x`, then
  exponentials, each an object with a customer of its own;
- which results of van der Hoeven (2006) and Aschenbrenner–van den
  Dries–van der Hoeven (2017) are in reach constructively.

## What it assumes from elsewhere
- **[[formal-power-series]]**: the ℕ case and the `antidiag` hook.
- **[[regular-perturbation-expansions]]**: the singular-perturbation customer.
