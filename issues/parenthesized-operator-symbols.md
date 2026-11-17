---
title: Write an operator as a value, `(<=)`, in any expression position
status: closed
labels: [syntax, operators]
area: language
milestone: [none]
created: 2026-11-17
updated: 2026-11-17
---

The README's sort theorem said `s.SortedPerm(BitVec::unsigned_le, …)` where
the reader thinks `<=`. A bare symbol was already a value directly between an
argument list's delimiters (`f(<=, x)`,
docs/language/classes/operators-onto-classes-design.md §4), and
`λ (a: u8) (b: u8) => a <= b` converts to `BitVec::unsigned_le`, but there
was no spelling of the operation itself elsewhere.

## Log

- 2026-11-17: built. `(` operator `)` is the unapplied `OpSymbol` wherever an
  expression stands (parser only; resolution is the existing designation
  ladder at the checking position's carrier). Every `BitVec::unsigned_le`
  argument in `examples/sort/sort.hthr` (28 sites) checks as `(<=)`. Probes
  in `lib/_tests/std/data/sorting_tests.hthr`, one of them the refusal when
  the symbol is read before anything fixes the carrier
  (`List::insertion_sort((<=), [3, 1, 2, 1])`, the same as the bare `<=`).
  Tree-sitter: `operator_section`. Design note: operators-onto-classes §18.
