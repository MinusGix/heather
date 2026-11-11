---
title: "Derive a finite type's instance for an enum: the generator cannot build a match"
status: open
labels: [stdlib,derive,generators,finite]
area: tactics
milestone: [math-finite]
created: 2026-11-11
updated: 2026-11-11
---

Found by [[finite-types-and-enumeration]] (2026-11-11).

An enum's `Fintype` instance is mechanical
(`lib/_tests/std/data/fintype_tests.hthr`, `Color`): the constructor
list, a `match` with one `Inl(refl)` per constructor for completeness,
and one refuted equation per pair of constructors for `NoDup`. A
generator in `lib/std/tactic/derive.hthr` can produce the instance
declaration (`AsInstance`) and the list, but not the two proofs: the
reflected `Expr` (`lib/std/tactic/tactic.hthr`) has application, `λ`,
`Π` and equations, and no `match` or eliminator.

## Scope

- Give generators a way to build a case analysis over a named inductive:
  a `Match` node in `Expr`, or a request answering the type's eliminator
  as a handle ([[generator-ctors-open-types]] owns the neighbouring
  `Ctors` questions).
- `generate fintype(T);` for an inductive whose constructors have no
  fields, then for constructors whose fields are finite types (a sum of
  products of the fields' enumerations).
- The `NoDup` evidence is quadratic in the constructor count as written
  by hand. Generate it through an injection into `Fin(n)` (the
  constructor's index) and `List::nodup_map`'s converse, so it is linear.

## Done when

`generate fintype(Color);` replaces the hand instance in the probes, and
an opcode-sized enum (a few dozen constructors) derives within the
suite's rails.
