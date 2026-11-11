---
title: "Finite functions, finite maps and multisets, as what big operators range over"
status: open
labels: [stdlib,mathematics,finite]
area: mathematics
milestone: [math-finite]
created: 2026-11-10
updated: 2026-11-10
---

Area 1 of the 2026-11-10 ranking, third piece.

`lib/std/data/nat_map.hthr` is the only map, keyed by `Nat`. There is no
multiset. `big_operator.hthr` sums without a statement that the sum does
not depend on order.

## Scope

- Functions out of a finite type: extensionality as a decidable
  comparison when the codomain has one, tabulation and lookup as inverse.
- A finite map interface over a key type with decidable equality, with
  the list-backed and `NatMap` implementations as instances and the point
  update laws stated once ([[state-location-and-frame-kit]] owns those
  laws for stores; cite, do not copy).
- Multisets as lists up to `Perm`, with `count` as the complete
  invariant, union, and a fold over a commutative monoid that respects
  `Perm`.
- Sums and products over a finite type and over a multiset, as the
  meaning [[big-operator-semantics]] gives its notation.

## Done when

`big_operator.hthr`'s reindexing and reordering lemmas are instances of
the multiset fold, and [[finite-linear-algebra]] can state a dot product
over `Fin n` with no local sum lemma.

## What it assumes from elsewhere

- **[[finite-types-and-enumeration]]** owns the class.
- **[[big-operator-semantics]]** owns the notation.
