---
title: Finish the rationals' order: strict order, abs, monotone products, Archimedean
status: closed
labels: [stdlib,mathematics,order,setoids]
created: 2026-10-10
updated: 2026-10-14
---

Residue of [[positive-naturals-and-rationals]] (2026-10-10 round,
docs/setoid-rationals-round.md). `lib/std/rat.hthr` has `≤` (refl, trans,
antisymmetry modulo `≈`, total, respects `≈`), right addition monotonicity and
non-negative products. Still missing, and wanted by the real-number probes:

- strict `<` (as `¬(y ≤ x)` or a positive-difference form; decide which, with
  [[apartness-structures]] in mind) and its respect for `≈`;
- `abs`, the triangle inequality, and multiplication by a positive preserving
  `≤`/`<`;
- the Archimedean property, and `1/(n+1)` bounds the Cauchy-sequence probes
  use;
- an instance of [[constructive-ordered-field-interface]] once it exists.

Expected to lean on [[ring-normalization]] if that lands first.

## Log

- 2026-10-12: [[ring-normalization]] landed: equations are `ring` calls now; the order laws this issue owns want inequalities, filed as [[ring-inequalities]].
- 2026-10-14: LANDED (docs/rational-order-round.md). Strict `<` is the positive-difference form (cross-multiplied `Int` `<`), agreeing with `¬ ≤`; with `lt_respects`, mixed transitivity, trichotomy, cotransitivity, tightness, `le_dec` and a `Decide` instance. Binary `-`, `abs` (numerator's absolute value), `abs_le`, the triangle inequality, distance symmetry and `dist_triangle`. Scaling by a non-negative/positive factor and `mul_pos`. `archimedean`, `archimedean_inv`, and `inv_succ(n)` = 1/(n+1) with positivity, antitonicity and halves. The showcase proves the regular-Cauchy two-halves estimate. The ordered-field instance stays with [[constructive-ordered-field-interface]], which has no interface yet. Exposed: [[calc-over-order-relations]] (an inequality chain), [[omega-nested-projection-of-call]].
