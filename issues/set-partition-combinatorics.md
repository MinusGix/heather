---
title: Perfect matchings and the lattice of set partitions
status: open
labels: [stdlib,mathematics,combinatorics]
area: mathematics
milestone: [ml-gaussian-states]
created: 2026-10-21
updated: 2026-10-22
---

Perfect matchings of a finite set (their count `(2k−1)!!`), set partitions
of a finite set ordered by refinement, the interval structure of that
lattice, and its Möbius function `μ(σ, ⊤) = (−1)^{k−1}(k−1)!`. Customers:
Wick's theorem and cumulants ([[ml-gaussian-states]]). Non-crossing
partitions (free cumulants) are a natural later extension.

Design note from Wick: index blocks by finite subsets, not by ordered tuples
of positions; its tuple-indexed first version produced a large layer of
`Fin.cast` plumbing that its later refoundation deleted.

## What it assumes from elsewhere

- **[[finite-set-client-design]]** owns finite sets. Assumed here: finite
  subsets of a finite type with decidable membership.

## Log
