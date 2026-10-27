---
title: "Hurwitz series and jets: calculus in coinductive form"
status: open
labels: [stdlib,mathematics,analysis]
area: mathematics
milestone: [math-reals,ml-layers]
created: 2026-10-27
updated: 2026-10-27
---

Layer B of `docs/analysis-foundations-design.md` (§5), with the
representation decided in §3.4. A series is its coefficient function in the
Hurwitz convention (`coeff(n)` stands for the `n`-th derivative at the
point, with no factorial), the derivative is the shift, and bisimulation is
the proof principle. Everything computes at `Int` and at `Rat`.

Scope:

- `Hurwitz<A> { coeff: Nat → A }` over a commutative ring, with
  coefficientwise `≈`, pointwise `+`, and the product as binomial
  convolution over a named `antidiag(n)` (the transseries hook, §11);
  a `CommRingOfInt` instance so `ring` works on series;
- `Hurwitz::coind`: equal heads and bisimilar derivatives give `≈`, proved
  by induction on the index; the Leibniz rule for the shift;
- definitions by ODE as course-of-values recursion: `exp`, `sin`, `cos`
  over `ℤ`, with `s² + c² ≈ 1` and the `exp` addition law (one-variable
  form `exp(a·t)·exp(b·t) ≈ exp((a+b)·t)`) by coinduction;
- polynomials (degree bound as data) and `Jet(A, N)`, with truncation a
  ring homomorphism; composition when `coeff(0) ≈ 0`;
- Newton lifting for inverses (unit constant term) and simple roots;
- the bridge to ordinary power series over a ℚ-algebra (`a_n / n!`);
- dual numbers: evaluating a polynomial at `x + ε` gives `(f(x), f'(x))`,
  the forward-mode AD theorem `ml-layers` wants.

Codata is not the representation in this round: the Leibniz product is
corecursion up to `+`, which Heather's guard refuses
(`issues/codata-nested-guards.md`). Revisit when that issue lands.

## What it assumes from elsewhere
- **[[finite-sums-and-products]]** and **[[finite-difference-calculus]]**:
  the exchange lemmas and the binomial coefficients with Pascal's rule.
- **[[ring-modulo-a-relation]]**: `ring` at a carrier's `≈`.
