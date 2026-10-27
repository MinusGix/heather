---
title: Difference calculus: telescoping, summation by parts, binomial theorem
status: open
labels: [stdlib,mathematics,analysis]
area: mathematics
milestone: [math-reals]
created: 2026-10-27
updated: 2026-10-27
---

Layer A′ of `docs/analysis-foundations-design.md` (§4): the exact discrete
calculus, at a commutative ring and without division.

Scope:

- `Δf(k) = f(k+1) - f(k)`; telescoping `∑_{k<n} Δf ≈ f(n) - f(0)` and its
  order form (`Δf <= g` gives `f(n) - f(0) <= ∑ g`);
- summation by parts;
- falling factorials and `Δ x^{\underline m} = m · x^{\underline{m-1}}`, with
  the power-sum closed form multiplied out;
- the geometric sum `(1 - r) · ∑_{k<n} r^k ≈ 1 - r^n`;
- binomial coefficients, the binomial theorem at a commutative semiring
  (through `of_nat`), Vandermonde;
- Newton's forward-difference formula, the discrete Taylor theorem.

Acceptance: `Series::decay` (or its core) is restated as an instance of the
geometric lemma; the binomial theorem is proved generically and probed at
`Nat`, `Int`, `Rat`.

## What it assumes from elsewhere
- **[[finite-sums-and-products]]** owns the range sum and its reindexing lemmas.
