---
title: Fixed arrays of words and constant tables in rt
status: open
labels: [native,compiler,representation]
area: heather-in-heather
milestone: [nh-front]
created: 2026-11-10
updated: 2026-11-10
---

`rt` has `Bytes(cap)`: a list of bytes in a buffer. A hash wants an
eight-word state, a sixteen-word schedule and a table of round constants; a
table-driven scanner wants a transition table. None is expressible in a
`runtime fn` today except as a flat record of words (which a call cannot
pass, [[function-ir-multi-word-calls]]) or as literals unrolled into the
code.

## Scope

- `rt::Ty` for `[BitVec(w); n]` (the surface's fixed vectors), held in a
  buffer of `n · w / 8` bytes, with element reads and writes at the
  element's width. `Bytes(cap)` is the `w = 8` instance.
- Byte order as a codec, not a convention: an element load is
  `BitVec::of_bytes_le` or `_be` of the buffer's bytes, each with its
  round trip (`lib/std/bitvec/bitvec_bytes.hthr`; [[codec-round-trips]]).
  SHA-2 reads its block big-endian, ChaCha20 little-endian.
- Constant tables: a closed `[BitVec(w); n]` value as read-only data
  beside the code (`Buffer.initial` is the static form), read by index.
- FunctionIR load and store nodes at widths 16, 32 and 64, with their
  cases of `Tm::lower_sound` over `function_ir_state`'s run.
- `for` over an array's indices as the existing loop shapes.

## Done when

A `runtime fn` that sums a `[BitVec(32); 16]` and one that reads
`K[i]` from a 64-entry constant table agree with their Heather functions
through the theorem, with a negative control (a big-endian load lowered as
little-endian is refused by the kernel).

## What it assumes from elsewhere

- **[[runtime-default-setup-soundness]]** owns `Get`, `Set` and `Fold` over
  bytes and the move of the theorem to `function_ir_state`'s run. Assumed
  here: that move.
- **[[source-buffers-as-views]]** owns where a buffer lives.
- **[[x86-narrow-and-rotate-forms]]** owns the 32-bit load and store forms.

## Log

- 2026-11-10: A second customer for constant tables: the scanner's automaton (`lib/lang/lexer/lexer_scan.hthr`) is a transition table written as about ninety chains of byte comparisons, because compiled code has no table to index. As a table it is a class per byte (256 entries) and a next state per (state, class), two loads a byte where the chains are a dozen compares and branches; it is also what [[lexical-grammar-as-data]] would generate. The family split in `scan_family` is the same table's first level, done by hand.
