---
title: Restate the generic analysis files with numerals and minus
status: blocked
labels: [stdlib,ergonomics]
area: mathematics
milestone: [math-classes]
blocked-by: [generic-theorem-implicit-points]
created: 2026-11-08
updated: 2026-11-08
---

Since [[class-carrier-arithmetic-surface]], a section over `OrderedField`
writes `0`, `1`, `2`, `-x`, `x - y` and `e / 2`, and `ring`/`linarith` read
them. Only real_fn's bound lemmas were restated in that round
(`OrderedField::half_pos`: `0 < e → 0 < e / 2`); real_fn, sequence,
closed_interval, supremum, real_fn_limit and the ordered-field theory still
spell `K.unit`, `K.multiplicative.unit` and `x + K.inv(y)` (hundreds of
occurrences, docs/stdlib-math-awkwardness-survey.md §2).

The survey's §13 asks for this restatement to wait for
[[generic-theorem-implicit-points]], so each statement is rewritten once,
with both its numerals and its implicit points.

## Acceptance

- The generic analysis files state their theorems with numerals and `-`
  where the mathematics writes them, and the `K.unit`/`K.inv(` counts in
  them drop accordingly.
- `scripts/timings --diff` on each restated file: count columns may move
  (the terms are one δ-step longer), seconds within noise.
