---
title: Display a type by the name the program wrote for it
status: closed
labels: [diagnostics]
area: heather-in-heather
created: 2026-11-03
updated: 2026-11-06
---

A `def` at a universe and a width family are expanded where they are read
(docs/fixed-width-integers-design.md §2): `u8` is `BitVec(8)` to every reader,
so a diagnostic about a `u8` says `BitVec(8)`, and one about an `i64` says
`SInt(64)`. Correct, and the honest spelling, but not the program's.

Wanted: the display respells a type that is the expansion of a type name in
scope by that name, preferring the spelling the declaration wrote. The
expansion is a pure function of the name, so a table from expanded type to
name, filled at each expansion, is enough; the question is which name wins
when two are in scope (`u8` and a program's own `Byte`).

## Log

- 2026-11-06: Done. The display keeps a table of the type names the program wrote
  (`Memos::type_names`), filled where `lower_type_value`/`try_type_value_app`
  expand a name and read off the definition's body once per name: a type
  constructor at closed value arguments, or a one-argument family
  (`λ n. D(n)`), possibly through other `def`s. The speller respells an
  instance it already recovers by the entry: `u8`, `i64`, `i(n)`, `List<u8>`,
  `Byte`; a family covers unwritten widths (`BitVec(16)` reads `u16`). Which
  name wins: the most recently written that still resolves to the same `def`
  and is not hidden by a local, which inside a declaration is the one that
  declaration wrote. Reader flavours only. A computed width stays unreduced
  (`u(add(8, 8))`). Design: docs/surface-type-display-design.md §5.1; probes
  lib/_tests/std/bitvec/type_names_tests.hthr.
