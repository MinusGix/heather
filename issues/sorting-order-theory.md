---
title: Lexicographic order, generic Sorted and permutations
status: closed
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

## Log

- 2026-11-09: done. `lib/std/data/perm.hthr`: `Perm` defined by recursion on
  the left list through `Picks(x, ys, rest)` (no indexed family: the
  textbook relation's indices are computed, which the generator refuses);
  equivalence, `::`/`++` congruences, `perm_swap`, `perm_middle`,
  `perm_append_comm`, `perm_cons_inv`, membership and length, and
  `perm_iff_occurrences` at `DecEq` (generic `List::occurrences`).
  `lib/std/data/sorting.hthr`: `List::Sorted(R)` (adjacent pairs, head below
  every member under a preorder), `insert_ordered`/`insertion_sort` over
  `DecidableRel(R)` proved sorted (with `Total`), a permutation, and stable
  (`insertion_sort_stable`, through any filter whose selected elements
  chain); `sorted_perm_eq`/`sorted_perm_unique` under a `PartialOrder` (no
  decider needed); `List::Lex(R)` (`LexAt`) a preorder, decided, a total
  preorder and a linear order, as constructors and as instances. New
  classes: `DecidableRel` (relation_props), `TotalPreorder` (order);
  `DecidableRel` at `Nat::Le`/`Int::Le`, and `LinearOrder` +
  `DecidableRel` at `BitVec::unsigned_le` (bitvec_nat). `list_algos`'
  `Sorted`, `insert`, `isort`, `count` and every theorem are one-line
  instances. `sort`'s spec is stated in `line_tools`
  (`byte_sorted_spec`, `sort_spec_unique`); the probes check `sorted_out`
  meets it at closed inputs, and the theorem at every input is
  [[sort-sorted-out-correct]].
- Gaps met on the way (filed where they are general):
  [[pattern-variables-not-rewritable]] (a list pattern's variables are not
  locals to `subst`, and `rewrite` misses them; every head case became a
  helper lemma), [[declaration-partial-application]] (`Lex(R)` had to be a
  λ wrapper over `LexAt`), [[deceq-instance-member-ambiguity]] (registering
  `DecEq<BitVec(n)>` breaks every `x.eq_dec(y)` call, so byte lines get no
  `occurrences` yet). Smaller, not filed: a literal list argument does not
  learn its element type from a later argument
  (`List::perm_sym<Nat>([3, 1, 2], [1, 2, 3], rotate())` needs the `<Nat>`);
  a `match` inside a `Type`-valued expression needs `as λ _ => Type`; and
  `xs.Sorted(R)` beside a bare `Sorted` in scope is refused as ambiguous
  (list_algos writes `List::Sorted(xs, R)`).

