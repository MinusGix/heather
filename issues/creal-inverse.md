---
title: Invert a regular Cauchy real apart from zero
status: closed
labels: [stdlib,mathematics,reals]
created: 2026-10-17
updated: 2026-10-17
---

Define the inverse of a regular Cauchy real apart from zero
(`lib/std/num/creal.hthr`), with `inv_respects` and `mul_inv`, and negative
controls at a zero argument.

A real apart from zero carries a gap: from some index s on, its terms stay
at least 1/(k+1) away from zero, on one side. The inverse reads the
reciprocal of x at an index past s and far enough out that the reciprocal's
Lipschitz constant (k+1)² stays inside the rate, e.g. the larger of s and
(k+1)²(2n+2) - 1. The gap is data, and the theorems that build `CReal::Lt`
keep their proofs sealed for a client to open
([[theorem-witness-unfolding]]), so the inverse computes.

Acceptance: `inv` for `x.Apart(CReal::zero())`, `inv_respects` (the two
apartness proofs may give different gaps), `mul_inv`, and refusals at a zero
argument.

## What it assumes from elsewhere

- **[[creal-multiplication]]** owns the product. Assumed here: `mul_close`
  and `same_close_far` compare terms read at independent far indices.
- **[[regular-cauchy-reals]]** owns `<` and apartness. Assumed here: a gap is
  `∃ k ∃ start` with the terms separated by 1/(k+1) from `start` on.
- **[[positive-naturals-and-rationals]]** owns `Rat::inv`. Assumed here: it
  is total with 0⁻¹ = 0, and `Rat::mul_inv` needs a nonzero argument.

## Log

- 2026-10-17: Done (docs/library/creal-inverse-round.md): `CReal::inv` at `x.Apart(CReal::zero())` reads the gap off the proof (`away_of_apart`) and x at index max(start, (k+1)²(n+1) + n); the factor 2 the body suggested is not needed. `inv_respects` (any two proofs), `mul_inv`, `inv_mul`, `ofRat_inv`, with the laws proved for an arbitrary gap first (`inv_gap`). Rational estimates (`dist_inv_le`, `inv_abs_le`, `scale_inv_succ_le`, …) in rat.hthr. Tests refuse a gap at zero and the termwise reciprocal, and evaluate the gap and terms. Order facts about the inverse wait on [[creal-order-and-bishop-bridge]].
