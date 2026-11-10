---
title: "Cardinality of finite types, injections and bijections, pigeonhole"
status: open
labels: [stdlib,mathematics,finite]
area: mathematics
milestone: [math-finite]
blocked-by: [finite-types-and-enumeration]
created: 2026-11-10
updated: 2026-11-10
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
