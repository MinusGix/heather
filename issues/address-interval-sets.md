---
title: Address intervals and interval sets, with a packing lemma
status: open
labels: [memory,native,order]
area: mathematics
milestone: [hih-memory-model]
created: 2026-11-09
updated: 2026-11-09
---

`lib/std/machine/memory.hthr` states span facts pointwise (`Space::Distinct`,
`Space::Apart` quantify over offsets), and each region kind re-proves that an
offset below the top is addition and that two spans are apart:
`BitVec::space_apart`/`_above`, `DataRegion::toNat_at`/`perm_from`/`allows`,
`Layout::buffer_apart` with `List::total_take_nth`/`total_take_apart`
(prefix sums by hand), `scratch_below_stack`, `Homes::Apart`,
`arena_cells_within`. About 140 citations.
`docs/native-mathematics-survey.md` §4; survey rank 4.

## Scope

- Half-open intervals `[a, a + k)` in a `Space` with a no-wrap condition:
  containment, disjointness, adjacency, split and concatenation, decided by
  endpoint comparison; `Apart`/`Distinct` as corollaries.
- Finite unions of intervals as values (sorted, disjoint) with computed
  union, intersection and difference, proved: a footprint is data.
- A packing lemma: sizes laid out consecutively from a base give pairwise
  disjoint intervals at the prefix sums (`Layout`, frames, scratch, arena).

## Done when

`Layout::buffer_apart` and `BitVec::space_apart` are instances of the
packing and disjointness lemmas, and [[wp-view-separating-product]] states
its footprints with them.

## What it assumes from elsewhere

- **[[wp-view-separating-product]]** owns the product of views. Assumed
  here: only that it needs footprints and their disjointness.
- **[[state-location-and-frame-kit]]** owns point-update laws of stores.
  Assumed here: nothing.
- **[[finite-set-membership-solver]]** closes the membership goals left
  after endpoints are compared.
