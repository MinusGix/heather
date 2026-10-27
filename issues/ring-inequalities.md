---
title: Prove polynomial inequalities with the ring normalizer
status: open
labels: [proofs,arithmetic,mathematics,solver,design]
area: tactics
milestone: [tac-arith]
created: 2026-10-12
updated: 2026-10-27
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

## Log

- 2026-10-14: [[rational-order-completion]] wrote `Rat::mul_le_mono_r`/`mul_lt_mono_r` as: scale the premise by `e·r` with `Int::mul_le_mono_r`, state each goal side equal to the scaled side with one `ring(den.mul_int(…))` each, and close with omega over product atoms (docs/rational-order-round.md). That is the first shape here done by hand; three lines per law, no monomial matching.
- 2026-10-15: Rat style review (PR #42): `Rat::mul_le_mono_r` and `Rat::mul_lt_mono_r` still state two long product equations by type (`let left: (… = …) = ring(…)`) only so omega can compare product atoms. `ring` at `≤` would make each a line.
- 2026-10-27: Siblings filed 2026-10-27: [[linarith-ordered-fields]] (linarith generic over ordered fields at their setoid equality, sharing this normaliser) and [[field-simp]] (clearing denominators before ring at fields).
- 2026-10-27: [[linarith-ordered-fields]] built `linarith` at ordered fields over `ring`'s reader (`ring::FieldReading`): the second shape here, for `≈` carriers. The Int-atom route (omega comparing ring-normalized products) is still this issue's.
