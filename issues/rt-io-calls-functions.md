---
title: A computation over Io calls a compiled function on its buffer
status: open
labels: [native,effects,runtime]
area: heather-in-heather
milestone: [nh-effects]
created: 2026-11-11
updated: 2026-11-11
---

A computation over `Io` (`ETm`, `lib/native/runtime/rt_io.hthr`) can
bind pure terms and call Linux. It cannot call a compiled function that
reads or writes one of its buffers, so a tool written as one `runtime
fn` over `Io` cannot hand the bytes it read to a loop like `raise_span`;
`tr` does that from the builder. U4 step 4c-4 made the layer's theorems
hold beside functions that write (`Writers::Still` among
`functions_below`) and left this node out
(`docs/native-one-compiler-design.md` §3;
`docs/native-procedures-are-functions-design.md` §2.8 for why it is one
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
