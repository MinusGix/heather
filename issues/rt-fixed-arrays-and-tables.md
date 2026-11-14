---
title: Fixed arrays of words and constant tables in rt
status: open
labels: [native,compiler,representation]
area: heather-in-heather
milestone: [nh-front]
created: 2026-11-10
updated: 2026-11-14
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
- 2026-11-14: Taken up for the scanner's table (Minus chose this route for [[lexical-grammar-as-data]]: constant tables first, then the scanner as one generated transition table; SHA-256's `K` is the other customer, through the optimizer thread). Design for the constant-table half, agreed with the optimizer's owner:
  - **A table read is a pure FunctionIR node**, not a load on the threaded state: `TableRead(width, output, table, index)` means `values(width, output)` is entry `index` of a table the program carries, so a read at a known index folds to a constant by one rule and moving or merging one needs no aliasing argument. Byte order is not in its meaning: it is fixed when the lowering lays the table out.
  - **Total by construction** (Minus 2026-11-13: no junk values): a table has `2^k` entries and the index port is `k` bits wide, so every index is in range with nothing to prove; a table of another length is padded to the next power of two by whoever builds it (a scanner's (state, class) table is laid out that way anyway).
  - **Lowering**: the entries as 64-bit words after the code (`Site.last`), the base from `LEA r64, [rip + disp32]` (native-library-exports-design §8: one instruction form, one premise that the bytes after the code read as data as well as fetch), then the existing `WordLoad` at `base + 8·index`.
  - **Order**: (1) the `LEA` form in the x86 model, decoded, encoded and stepped; (2) the node, its equation and its lowering case with the premise threaded through `compiled_returns`; (3) the source side, a closed table read in a `runtime fn`; (4) the export placing the bytes in the `.s`. Wider loads from mutable buffers (16/32/64 with a byte-order tag) are a separate piece: one constructor with a width, not three.
