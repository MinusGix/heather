---
title: Prove polynomial inequalities with the ring normalizer
status: open
labels: [proofs,arithmetic,mathematics,solver,design]
created: 2026-10-12
updated: 2026-10-12
---

`ring` (docs/ring-normalization-design.md) closes equations only. The
regular-Cauchy estimates the reals need ([[regular-cauchy-reals]]) are
polynomial *inequalities* in several variables, and the rationals' order laws
(`Rat::add_le_mono_r`, `Rat::le_trans`) still state each monomial equation by
hand so that `omega` can treat products as atoms.

Two shapes, to decide:

- **`ring` at `≤`/`<`**: prove `lhs ≤ rhs` when `rhs − lhs` normalizes to a
  constant that is nonnegative, or to a sum of terms each nonnegative by a
  hypothesis or a square. Small, and covers the monotonicity laws.
- **`linarith` over ring-normalized atoms**: normalize every hypothesis and the
  goal, read each distinct monomial as one atom, and hand the linear problem
  to the existing Fourier–Motzkin/omega machinery; with products of
  hypotheses (degree two) this is the `nlinarith` heuristic. Needs
  [[shared-arithmetic-reflection]]'s solver-neutral input boundary.

## What it assumes from elsewhere

- **[[ring-normalization]]** owns the normalizer. Assumed here: only
  `RingExpr::sound` and the reifier's atom table.
- **[[omega-linear-arithmetic]]** owns omega. Assumed here: nothing yet; the
  second shape would consume it.
