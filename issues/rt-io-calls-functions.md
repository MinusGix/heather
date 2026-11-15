---
title: A computation over Io calls a compiled function on its buffer
status: open
labels: [native,effects,runtime]
area: heather-in-heather
milestone: [nh-effects]
created: 2026-11-11
updated: 2026-11-12
---

A computation over `Io` (`ETm`, `lib/native/runtime/rt_io.hthr`) can
bind pure terms and call Linux. It cannot call a compiled function that
reads or writes one of its buffers, so a tool written as one `runtime
fn` over `Io` cannot hand the bytes it read to a loop like `raise_span`;
`tr` does that from the builder. U4 step 4c-4 made the layer's theorems
hold beside functions that write (`Writers::Still` among
`functions_below`) and left this node out
(`docs/native/native-one-compiler-design.md` §3;
`docs/native/native-procedures-are-functions-design.md` §2.8 for why it is one
node and not a merge of the two layers).

## Scope

- An `ETm` node: function `f` of the world on a buffer variable and word
  variables, binding its answer; the buffer's earlier variables gone
  afterwards, as after a read (`Loc`'s `Gone`), and a new variable naming
  the bytes the function left.
- Its meaning: the function's (`CompileSpan`'s run for a writer, the
  pure meaning for a reader), the world unchanged.
- Its lowering: a `Compute` of a region `Call`, and its case of
  `ETm::lower_sound` from `program_writers`; the `Still` hypothesis then
  ranges over the functions pure terms call and not over this node's.
- The reflector reads a call of a `runtime fn` on a buffer as this node.
- The limit it inherits: a program lends a function a prefix of its
  buffers, so the buffer handed over is the file's first until
  [[source-buffers-as-views]].

## What it assumes from elsewhere

- **[[native-one-compiler]]** owns `program_writers` and the stillness
  theorems. Assumed here: only `program_writers_stills`.
- **[[effects-uniqueness-surface]]** owns the reflector and `ETm`.

## Done when

`tr` is one `runtime fn` over `Io` that reads, calls `raise_span` on
what it read and writes it, passes its GNU tests, and a control that
reads the buffer's old variable after the call is refused by the
lowering.

## Log

- 2026-11-12: The node is built (`docs/native/native-one-compiler-design.md`
  §2.6, 4c-5). `ETm::Lend(f, cap, buf, args, body)` over a table of lent
  functions (`Lent`, `rt_io.hthr`); its lowering is a region `Call` of
  function `w.sigs.len() + f`, sound under `ETm::LentsAgree` (the
  program's function, lent the first buffer, answers as the table's run).
  `tr` is one `ELoop` over `Io` that reads, lends the bytes to
  `raise_span` and writes what it left; it reads as its meaning
  (`tr_reads`), compiles (`tr_lend_source`), and a native gate holds it
  to GNU tr. Refused: a write of the read's old variable after the call,
  a loop rebinding the buffer to it, a second buffer, a wrong arity, an
  unknown function (`lib/_tests/native/runtime/rt_io_lend_tests.hthr`).
  A loop condition's one-bit move did not compile; a bit its region's
  last node writes now stays in that port (`ETm::placed`). Left: the
  reflector reading a call of a `runtime fn` on a buffer as `Lend`. It
  needs `rt_reflect`'s reading of a call's `.after` and the effectful
  reflector's loops, which it does not read yet, so `tr` is written as an
  `ELoop` term, not reflected from its surface method. Found:
  [[rt-io-exit-on-failed-write]], [[rt-io-bit-variable-condition]],
  [[rt-io-loop-word-bound]].
