---
title: Make ring certificates cheaper for the kernel
status: open
labels: [proofs,arithmetic,performance]
created: 2026-10-12
updated: 2026-10-12
---

A `ring` certificate's kernel cost is the in-language normalizer's evaluation
(docs/ring-normalization-design.md §5). Monomials are dense exponent vectors
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

Measure through `scripts/perf ab --source-patch` over `lib/std/rat.hthr`; the
gate column per item is the one that moved.

## What it assumes from elsewhere

- **[[ring-normalization]]** owns the tactic and the certificate shape.
  Assumed here: only that the certificate is `sound`/`sound_with` with `refl`.
