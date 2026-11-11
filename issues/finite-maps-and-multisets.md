---
title: "Finite functions, finite maps and multisets, as what big operators range over"
status: open
labels: [stdlib,mathematics,finite]
area: mathematics
milestone: [math-finite]
created: 2026-11-10
updated: 2026-11-11
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

## Log

- 2026-11-11: First round, the multiset and finite-type folds.
  `lib/std/algebra/finite_fold.hthr`: over a commutative monoid the fold of
  a list respects `Perm` (`CommMonoidRel::fold_picks`, `fold_perm`,
  `fold_map_perm`), so it is a function of the multiset;
  `MonoidRel::over(op, f)` is the fold over a finite type, equal along every
  duplicate-free complete list (`over_enumeration`), with `over_cong`,
  `over_unit`, `over_op`, reindexing along a bijection of finite types
  (`over_reindex`), the instances' decompositions (`over_fin` = the range
  fold, `over_option`, `over_or`, `over_pair`), Fubini (`over_swap`) and a
  semiring's factor (`Semiring::mul_over_l`, `over_mul_r`). `perm.hthr`
  gains `picks_map` and `perm_map`, `fin.hthr` `Fin::to_nat` with its bound,
  `fintype.hthr` the pointwise comparison of functions out of a finite type
  (`Fintype::agree`, `Agree` for `decide`). The multiset's complete
  invariant was already there (`List::perm_iff_occurrences`). Probes in
  `lib/_tests/std/algebra/finite_fold_tests.hthr` state a dot product over
  `Fin(n)` with additivity and homogeneity from these laws alone, which is
  the second half of "done when".

  Remaining: the finite map interface with `NatMap` and a list-backed
  instance, tabulation and lookup as inverses, and `big_operator.hthr`'s
  `range_perm` re-derived from `fold_perm` (it is still the Fubini and
  Kronecker-delta proof; the route is `over_fin` then `over_reindex` at
  `Fin(n)`, which needs the bijection of `Nat` below `n` carried to
  `Fin(n)`: a `Fin::of_nat` with its round trips).
