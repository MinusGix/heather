---
title: Conditions whose proofs are interchangeable: squashed parameters
status: open
labels: [elaboration,sprop,language]
area: language
created: 2026-11-14
updated: 2026-11-14
---

A parameter or field whose proofs are never compared: two calls that differ
only in a found proof are equal by `refl`. Heather keeps proofs relevant, so
a search that finds two terms for one condition (a `decreases` body's
companions, a value holding a proof) gives two calls that do not convert.
PR #607 worked around it by lifting found proofs out of `decreases` bodies
(`measure::lift_found`) and by defining `Vec::at` as the total read.

Design and status: `docs/strict-conditions-design.md`. The condition's type
is `∥P∥`; the kernel's squash irrelevance already makes the arguments
convertible at an opaque head (no kernel change), and the elaborator
accepts a proof of `P` (a search, a tactic, or an inferred proof) where
`∥P∥` is expected.

## Done when

- Two `v.at(i, inside := p)` and `v.at(i, inside := q)` are equal by `refl`
  with the head opaque, with a negative control (probes:
  `lib/_tests/std/core/squash_conditions_tests.hthr`).
- A probe shows the lifting is unnecessary for a squashed condition.
- The note says what retires the lifting.

## Open for Minus

1. The surface: the type `∥P∥` alone, or a binder marker as sugar.
2. The release bridge `∥Empty∥ → Empty` (kernel; note §4.2), which makes
   every decidable condition recoverable and lets `vector_index` take its
   bound squashed.
3. Retiring `measure::lift_found` (note §5).
