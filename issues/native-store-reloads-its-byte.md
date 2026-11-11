---
title: The function compiler's store reloads the byte it stored
status: open
labels: [native,compiler,codegen]
area: heather-in-heather
milestone: [nh-library]
created: 2026-11-11
updated: 2026-11-11
---

A `BufferStore` lowered by the function compiler
(`File::store_at`, `lib/native/function_ir/function_ir_lower_reads.hthr`)
is three pieces: the address formed in the output's register, a
`StoreByte` of the register holding the value, and a `LoadByte` of the
byte just stored back over the address. The load is there because the
store's output names the byte then there (`Node::Runs`) and the leaf
proves that output held in a register like any other node's.

In the code a byte map compiles to, nothing reads that output, so the
load is one dead instruction per store.

## Options

- A store whose output nothing reads ends at the `StoreByte`. The
  register its placement names is still needed, since the address is
  formed there, so the placement says both: the register and that the
  output is dead (the planner knows what is live after a node,
  `plan_block`). The file after the leaf then holds nothing in that
  register, and the proof is the first two moves of `store_emits`. The
  meaning is unchanged: the output still names the byte, and only the
  file's claim that a register holds it is dropped.
- Where the output is read, a `MOVZX` from the value's register gives
  the same word with no memory read (`byte_word(low_byte(v))`), which
  needs `MOVZX r64, r8` in the assembler's instruction set and its
  `Moves` lemma.

The first covers every store whose output is dead, which is every store
of a byte map. Do it when a byte map's code is measured, not before.
