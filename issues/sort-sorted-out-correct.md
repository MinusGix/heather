---
title: Prove sort's sorted_out meets its specification at every input
status: open
labels: [native, lists, order]
area: heather-in-heather
milestone: [nh-heap]
created: 2026-11-09
updated: 2026-11-09
---

`lib/native/runtime/line_tools.hthr` states what `sort` promises: the lines
it writes are `lines.byte_sorted()` (the one sorted permutation under
`List::Lex(BitVec::unsigned_le)`, `List::sort_spec_unique`), each followed by
a newline. `sorted_out` computes something else, by repeated selection with
the line's place as a tie-break (`LinePick::prev_in`), and the probes in
`lib/_tests/native/runtime/line_tools_tests.hthr` check the two agree only
at closed inputs (`sorted_out_meets_spec`).

## Done when

`theorem List::sorted_out_spec(lines): lines.sorted_out() =
lines.byte_sorted().with_newlines()` at every `lines`, or `sorted_out`
replaced by `byte_sorted` if the native front end compiles it.

## What it needs

- `List::bytes_before(a, b) = True` reflects the strict part of
  `LexAt(BitVec::unsigned_le, a, b)` (it is written with `for`/`return`, so
  this is first a lemma about the loop's lowering).
- `prev_in` finds the greatest element strictly below `last` in the
  (line, place) order, which is linear because places are distinct; then
  the walks enumerate the input in that order, so the output is sorted and a
  permutation, and `sort_spec_unique` makes it `byte_sorted`.
