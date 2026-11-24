---
title: A runtime fn over a span of any codec's elements with a run-time count
status: open
labels: [native,runtime,layout]
area: heather-in-heather
milestone: [nh-library]
created: 2026-11-24
updated: 2026-11-24
---

A `runtime fn` can hold a span of bytes with a run-time count (`Bytes(n)`)
and a laid record whose arrays have a count the type fixes, but not a span
of any other element whose count is a word: `mut t: [u64; 8]` as a
parameter "has no runtime layout" (ledger row 11, `port_pred_limbs`), and
nothing spells "`n` words" with `n` a word.

Design: docs/native/rung2-spans-design.md §3. `Span<A>(n)` is `Bytes(n)`'s
record for any element with an `Accessor` (`stored_accessor.hthr`): a
`List<A>` and its length proof, `s[i]` and `s[i] := e` under a found proof.
Its meaning is held (`rt_held`'s shape): the span's bytes are the codec's
`put` of each item at `i * stride`, and the leaf cases are the accessor's
laws at an open base and count, which the class already states (`reads_at`,
`writes_at`). New: the codec of a run-time count beside `Stored::array`, its
holds relation, the reflector's reading of `at`/`put` on it, and the
generator's `runs_held` at it.

## Done when

`port_pred_limbs` (a borrow walk over `numeral`'s limbs) is written over a
`Span<u64>(n)` and compiles in the ledger with a run by `refl`, a span of a
laid record's entries is read and stored at a found index, and an index
without a proof is refused with the found-proof message.
