---
title: Harmonic numbers and Stirling as asymptotic expansions
status: open
labels: [mathematics,analysis,showcase]
area: mathematics
created: 2026-10-27
updated: 2026-10-27
---

The showcase of `docs/library/analysis-foundations-design.md` §9: expansions at
`n → ∞` that a Taylor-first library cannot state.

Scope:

- `H_n = log n + γ + 1/(2n) + O(1/n²)`, with `γ` defined as the limit of
  `∑ (1/k - log(1 + 1/k))` (explicit tail, no integral);
- the Bernoulli numbers as coefficients of `x/(e^x - 1)`;
- Stirling's expansion of `log n!` to a fixed order with its remainder, from
  the Euler–Maclaurin remainder in summation-by-parts form.

## What it assumes from elsewhere
- **[[certified-expansions]]** and **[[power-series-evaluation]]**.
- **[[interval-log-and-reduction]]**: `log` with its laws.
