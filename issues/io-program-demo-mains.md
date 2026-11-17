---
title: The sort and binary-search demos as runtime fn main programs with no C
status: open
labels: [native,effects,runtime,demo]
area: heather-in-heather
milestone: [nh-effects]
blocked-by: [io-program-prints-output]
created: 2026-11-16
updated: 2026-11-16
---

The UTF-8 demo is one ELF with no C (`examples/utf8/utf8check.hthr`, #698).
`examples/sort` and `examples/binary-search` still link a C `main.c` around
the compiled function.

## Scope

- sort: read stdin into a buffer, `sort_in_place` it as a lent span, write
  it back; theorem from `sort_in_place_sorts`. Needs printing
  ([[io-program-prints-output]]).
- binary search: needs its query and haystack read from input (parsing
  decimal words or a fixed binary format); theorem from
  `lower_bound_splits`.
- Gates as `utf8_program_exits_as_rust_decides`: reading the library
  gate's store (`PREREQUISITES` readers in scripts/run-test-targets.mjs),
  skipped in the fast lane.
- Each program's theorem stops where [[io-program-whole-theorem]] picks up.
