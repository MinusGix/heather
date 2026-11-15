---
title: Give regular Cauchy reals a non-strict order and the Bishop equality bridge
status: closed
labels: [stdlib,mathematics,reals,order]
created: 2026-10-16
updated: 2026-10-17
---

Give `CReal` a non-strict order and connect its `≈` to Bishop's pointwise
equality.

- `≤` as `¬(y < x)` (Bishop's), with reflexivity, transitivity, the mixed
  transitivities with `<`, and antisymmetry modulo `≈` (which is tightness).
- The Bishop bridge: `x ≈ y` iff `|x_n - y_n| ≤ 2/(n+1)` for every n. The
  pointwise-to-eventual direction is immediate. The other direction needs
  the rational lemma "a ≤ b + 1/(k+1) for every k gives a ≤ b"
  (`Rat::same_of_close`'s argument, one-sided) and a three-term estimate
  through a far index.
- Order and addition: `add_lt_mono`, `add_le_mono`, positivity of a sum.

## What it assumes from elsewhere

- **[[regular-cauchy-reals]]** owns `<` as an eventual gap given as data.
  Assumed here: `lt_of_term` (one far index suffices) is the tool for
  building gaps.
- **[[constructive-ordered-field-interface]]** owns which of these become
  interface laws.

## Log

- 2026-10-17: `≤` landed with the multiplication round (docs/library/creal-multiplication-round.md): `CReal::Le` is `¬(y < x)` with reflexivity, transitivity, the mixed transitivities with `<`, antisymmetry modulo `≈` (tightness), `le_respects`, the embedding both ways, `Preorder` and the mixed `Trans` pairs. Remaining here: the Bishop bridge and `add_lt_mono`/`add_le_mono`/positivity of a sum.
- 2026-10-17: Bishop bridge both ways for ≈ (`same_of_bishop`/`bishop_of_same`) and for ≤ (`le_of_bishop`/`bishop_of_le`, Bishop's pointwise order), `add_lt_mono`/`add_le_mono` with their mixed forms and cancellation, Bishop's splitting `add_lt_cancel`, and the signs of a sum (docs/library/creal-order-round.md). Products against the order moved to [[creal-mul-order]].
