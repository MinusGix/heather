---
title: Formal power series, polynomials and jets over a commutative ring
status: open
labels: [stdlib,mathematics,analysis]
area: mathematics
milestone: [math-reals,ml-layers]
created: 2026-10-27
updated: 2026-10-27
---

Layer B of `docs/analysis-foundations-design.md` (§4): formal power series,
polynomials and jets over a commutative ring, all computing at `Rat`.

Scope:

- `PowerSeries<A> { coeff: Nat → A }` with coefficientwise `≈`, pointwise `+`,
  Cauchy convolution over a named `antidiag(n)` (the transseries hook, §10),
  a `CommRingOfInt` instance so `ring` works on series;
- polynomials (degree bound as data) and `Jet(A, N)` (≈ below `N+1`), with
  truncation a ring homomorphism;
- the formal derivative as a derivation; composition when `coeff(0) ≈ 0`;
- `exp` over a ℚ-algebra with `exp(a+b) ≈ exp(a)·exp(b)` (binomial theorem
  coefficientwise), `D exp ≈ exp`, `D f ≈ 0 ⇒ f ≈ const`, formal
  `sin² + cos² ≈ 1`;
- Newton lifting for inverses (unit constant term) and simple roots;
- dual numbers: evaluating a polynomial at `x + ε` gives `(f(x), f'(x))`,
  the forward-mode AD theorem `ml-layers` wants.

## What it assumes from elsewhere
- **[[finite-sums-and-products]]** and **[[finite-difference-calculus]]**:
  the exchange lemmas and the binomial theorem.
- **[[ring-modulo-a-relation]]**: `ring` at a carrier's `≈`.
