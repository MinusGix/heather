---
title: One notion of buffer in Source: static, borrowed, arena and frame storage as views
status: open
labels: [native,design,memory,function-ir]
area: heather-in-heather
milestone: [nh-library]
created: 2026-11-10
updated: 2026-11-11
---

A `Source` buffer is a numbered static slot in the ELF's data region
(`Source.buffers`, `Layout`). Three rounds have each needed something else
and each would build it separately:

- the arena: a line is a span of the arena buffer, so `Bytes` must lower as
  a view (buffer, offset, length) and not only as a whole buffer
  ([[runtime-fn-arena-lists]], log of 2026-11-02);
- an export: the source span and the hash state are memory the caller owns,
  at an address that arrives in a register ([[native-library-exports-design]]);
- a procedure: local scratch is a block of its frame.

## Scope

- A buffer as an address held in a word plus a capacity. Static, borrowed,
  arena and frame buffers are instances that differ only in where the
  address comes from and who may write.
- `Target::Placed`/`Held` and the byte nodes' lowering (`BufferLoad`,
  `BufferStore`) over an address word; `Layout`'s static buffers as the
  instance with a literal address.
- Footprints as span sets (`lib/std/data/set/span_set.hthr`): two views are
  apart when their spans are, decided by the endpoints.
- `rt`'s `Bytes` held as a view, so a slice costs no copy.

## Done when

One program reads a static buffer, a borrowed span and an arena line
through the same nodes and the same lowering case, with a negative control:
a store through a read-only view is refused by the judgment.

## What it assumes from elsewhere

- **[[native-library-exports-design]]** decides whether this is the notion
  to build. Assumed here: only that it is asked the question first.
- **[[function-ir-buffer-state-edges]]** owns byte nodes in S4 with
  registers held across them.
- **[[state-location-and-frame-kit]]** owns point updates of a store.

## Log

- 2026-11-11: What U5's step 5d (byte nodes on the shared lowering, [[native-one-compiler]]) would take today, read off the code after step 5c, and why it reads as part of this issue:

    - The shared leaf (`emit_leaf`, `function_ir_lower_calls.hthr`) takes a buffer's home as two values of its scope, address and length (`Lent`), and lowers a load or a store only where the path knows the index below the length (`File::bounded`). A program's byte node tests the index itself and reads the address off the layout (`Prog::byte_to`, `byte_from`). So the program side would keep its test and hand the access to the leaf with the home loaded as two immediates, which is this issue's "static buffers as the instance with a literal address".
    - The leaf's theorems are stated in the function compiler's frame: what a leaf leaves is `Stack::Trailed(lending, d, …)`, stores below offset `d + 64`, the 64 bytes at RSP being a function's spill slots. A statement's frame words sit exactly there since step 5b. No leaf stores to the stack, so the leaf theorems (`kept_block_emits` through `emit_leaf_runs`) hold at any bound; they would be restated over a bound `i`, with the `d` forms their instances at `d + 64`. The alternative, 64 bytes of slack in `Target.roomy`, moves the top theorem's `deep` for nothing a program uses.
    - The program side then proves a byte node from the lending it already gives its callees (`Target::lending`, `loan`, `in_memory`, `based_left`), with a register file and a valuation built by hand at the leaf, R10 named in the file since a leaf keeps only the callee-saved registers. That is longer than `goes_byte_to` and `goes_byte_from` are now: the machine fact shared is one MOVZX and one byte MOV.
    - So the step pays when the home is a value and not a layout constant, which is this issue. Built before it, the bridge is written for immediates and rewritten for words.
