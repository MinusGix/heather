---
title: Sum Euler's divergent series by nested continued-fraction enclosures
status: open
labels: [mathematics,analysis,reals,intervals]
area: mathematics
created: 2026-10-27
updated: 2026-10-27
---

`docs/analysis-foundations-design.md` §3.8: the first divergent series
summed end to end, with no integration. Euler's series
`E = ∑ (−1)ⁿ n! xⁿ⁺¹` is the formal solution of `x²E' + E = x`, and it has
the Stieltjes continued fraction `x/(1 + x/(1 + x/(1 + 2x/(1 + 2x/…))))`,
with partial numerators `⌈k/2⌉·x`.

Scope:

- `E` as a Hurwitz series defined by its ODE, and the formal identity
  relating the continued fraction's convergents to `E`. The convergents
  agree with `E` to an order that grows with the depth;
- for `x > 0` at `Rat`: the convergents alternate and nest, proved
  algebraically from the three-term recurrences;
- a rate for the widths, so that the value is a `CReal` built by nested
  enclosures. Carleman's condition gives convergence but not a modulus, so
  find one from the linear growth of the coefficients, or report what is
  missing;
- the result as an instance of [[summation-methods]] on Stieltjes series
  (regular, and linear on the class), with an `Enclosed` leaf so that
  `by intervals()` reads `E(1/10)`;
- probes: an enclosure of `E(1/10)` and `E(1)`, and the asymptotic
  reading (optimal truncation near `n ≈ 1/x` against the enclosure).

The identity with the Borel–Laplace integral `x·∫₀^∞ e^{−t}/(1 + xt) dt`
is [[borel-laplace-summation]]'s.

## What it assumes from elsewhere
- **[[formal-power-series]]**: definitions by ODE.
- **[[summation-methods]]**: the interface.
- **[[interval-creal-enclosures]]**: the enclosure checker.
