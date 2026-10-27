---
title: Finite sums and products over a commutative monoid modulo ≈
status: open
labels: [stdlib,mathematics,analysis]
area: mathematics
milestone: [math-reals]
created: 2026-10-27
updated: 2026-10-27
---

Layer A of `docs/analysis-foundations-design.md` (§3): finite sums and
products as folds over a commutative monoid modulo its relation, with one
theorem serving `∑` and `∏` through the semiring layers' `multiplicative` tag.

Scope:

- the range sum `MonoidRel::range(op, n, f)` by recursion on `n` (the shape
  `Series::sum` already has), and sums over `Fin(n)`, lists, rectangles,
  triangles and antidiagonals defined through it;
- laws modulo `≈`: congruence, split/shift, empty and singleton, reverse,
  permutation invariance (commutative), rectangle Fubini and the
  triangle-to-antidiagonal exchange, distributivity at a semiring;
- order laws at `OrderedAddGroup`: monotone, nonnegative, `|∑ f| <= ∑ |f|`;
- a carrier-level spelling (`Rat::sum(n, f)` or similar) until the binder
  production exists; probes in `lib/_tests` at `Nat`, `Rat` and an open carrier.

Acceptance: `Series::sum` is shown to be the range sum (a theorem, no
rewrite of series.hthr required), and the exchange lemma proves one
Cauchy-product coefficient identity at `Rat`.

## What it assumes from elsewhere
- **[[big-operator-semantics]]** owns the semantic comparison; assumed here
  only its finite route (generic folds), which the design note recommends.
- **[[notation-extensibility]]** owns the `∑ k < n, e` production; nothing here waits for it.
- **[[finite-set-enumeration-and-folds]]** owns folds over finite sets; assumed
  here only that an enumeration is a list.
