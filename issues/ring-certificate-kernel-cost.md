---
title: Make ring certificates cheaper for the kernel
status: open
labels: [proofs,arithmetic,performance]
area: tactics
created: 2026-10-12
updated: 2026-10-31
---

A `ring` certificate's kernel cost is the in-language normalizer's evaluation
(docs/tactics/ring-normalization-design.md §5). Monomials are dense exponent vectors
over the whole atom list, so every comparison and every monomial product walks
a vector as long as the highest atom index it mentions, and `sound_with`
normalizes both `lhs − rhs` and the multiplied hypotheses `D`. On the
rationals the laws that used to be short chains of named lemmas
(`Rat::mul_respects`, `Rat::add_respects`, `Rat::same_trans`) are now dearer
in the gate than they were, though the module checks faster overall because
their elaboration went.

Levers, none measured yet:

- sparse monomials (sorted `(index, exponent)` pairs), so a degree-four
  monomial over a dozen atoms is four entries, not twelve;
- normalizing `RSub(RSub(lhs, rhs), D)` once against `PZero` instead of two
  normal forms compared;
- ordering the atom table so the atoms that occur most get the low indices.

Measure through `scripts/perf ab --source-patch` over `lib/std/num/rat.hthr`; the
gate column per item is the one that moved.

## What it assumes from elsewhere

- **[[ring-normalization]]** owns the tactic and the certificate shape.
  Assumed here: only that the certificate is `sound`/`sound_with` with `refl`.

## Log

- 2026-10-31: Data point from exp-log-grid-gap (2026-10-31): the Padé three-term relation between series terms, stated as one field identity with x and six reciprocal atoms (inv_succ of linear forms in n, k), ran out of the kernel's fuel. The same relation, factored as exp's term times x-free weights and with the reciprocals bound by let (atoms to ring), checks well inside it. The cost grew with the number of distinct reciprocal atoms the normalizer clears together, not with the polynomial degree.
- 2026-11-05: gardener: cites a file it shares with [[class-inherited-field-implementations]] (`lib/std/num/rat.hthr`); [[setoid-roadmap-and-resumption]] (`lib/std/num/rat.hthr`).
