---
title: "Cardinality of finite types, injections and bijections, pigeonhole"
status: closed
labels: [stdlib,mathematics,finite]
area: mathematics
milestone: [math-finite]
blocked-by: [finite-types-and-enumeration]
created: 2026-11-10
updated: 2026-11-11
---

Area 1 of the 2026-11-10 ranking, second piece.

## Scope

- `card` of a finite type as the length of its enumeration, independent of
  the enumeration chosen (through `Perm`, `lib/std/data/perm.hthr`).
- Injective, surjective and bijective maps between finite types as
  records with their laws (`relation_props.hthr` has only the bare
  propositions); `card` is monotone along injections and equal along
  bijections; `card` of products, sums and `Option`.
- Pigeonhole: a map from a larger finite type to a smaller one identifies
  two points, with the two points computed.
- A strictly ascending chain in a finite type is no longer than its
  cardinality. This is the termination argument Kleene iteration needs
  ([[galois-connections-and-checked-fixpoints]]) and the bound on
  derivative states ([[regular-languages-by-derivatives]]).

## Done when

The chain bound is stated once and cited by one fixpoint iteration.

## What it assumes from elsewhere

- **[[finite-types-and-enumeration]]** owns the class.

## Log

- 2026-11-11: Built. `lib/std/data/fintype_card.hthr`: `Fintype::nodup_len_le` (a duplicate-free list is no longer than the type), `card_unique` and `enumeration_perm` (the cardinality and the enumeration up to `Perm` do not depend on the instance's list), `card_le_of_injective`, `card_le_of_surjective` (surjectivity stated with its preimage), `card_eq_of_bijective`, `card_option`/`card_pair`/`card_or`/`card_fin`, `pigeonhole` (codomain with `DecEq`), `Fintype::collision` as the function that evaluates to the two points with `collision_sound`, and `chain_len_le` for a list `Sorted` at an irreflexive transitive relation. None of the counting decides equality: it stands on `List::nodup_sub_len` in `perm.hthr` (remove one element at a time through `Picks`), with `picks_nodup` and `nodup_perm` beside it. `list.hthr` gained `Dup`, `mem_dec`, `nodup_dec`, `dup_map`, `len_product` and `collision`; `sorting.hthr` gained `sorted_below` and `sorted_nodup`; `Bool` and `Fin(n)` gained `DecEq` instances (`Fin::eq_dec`).

  Residue, with owners: the chain bound's first citation by a fixpoint iteration is [[galois-connections-and-checked-fixpoints]]'s; the derivative automaton's is [[regular-languages-by-derivatives]]'s. `DecEq` at `Option`, `Pair` and `Or`, and `card` of `BitVec(n)` as `2^n`, were not needed here and go with [[finite-maps-and-multisets]], which wants decidable keys.
