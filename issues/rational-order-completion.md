---
title: Finish the rationals' order: strict order, abs, monotone products, Archimedean
status: open
labels: [stdlib,mathematics,order,setoids]
created: 2026-10-10
updated: 2026-10-10
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
