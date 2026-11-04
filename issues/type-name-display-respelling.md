---
title: Display a type by the name the program wrote for it
status: open
labels: [diagnostics]
area: heather-in-heather
created: 2026-11-03
updated: 2026-11-03
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
