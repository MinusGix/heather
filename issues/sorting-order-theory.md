---
title: Lexicographic order, generic Sorted and permutations
status: open
labels: [order,lists,native]
area: mathematics
milestone: [nh-heap]
created: 2026-11-09
updated: 2026-11-09
---

`lib/lang/list_algos.hthr` has `Sorted`, `isort` and `count` at `Nat` only.
`sort` (an `nh-heap` target), `uniq` and `comm` compare byte strings and
need the theory generic. `docs/native-mathematics-survey.md` §8; survey
rank 8.

## Scope

- The lexicographic order on `List<A>` from an order on `A`, proved a total
  preorder (and a linear order from a linear one).
- `Sorted` generic in the relation; a permutation relation (equivalence,
  congruence for `++`, characterised by counts at decidable equality).
- Two sorted permutations of one list are equal under a linear order, so a
  spec names the output; stability for keyed sorts.

## Done when

`sort`'s spec is stated as sorted-permutation under the byte-lexicographic
order, and the `Nat` lemmas in `list_algos` are instances.
