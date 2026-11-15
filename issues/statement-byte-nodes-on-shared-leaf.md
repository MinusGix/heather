---
title: A statement's byte nodes through the shared leaf (U5 step 5d)
status: open
labels: [native,ir,proofs,compiler]
area: heather-in-heather
milestone: [nh-library]
created: 2026-11-12
updated: 2026-11-12
---

A statement of `Source` lowers its own byte nodes (`BufferLoad`, `BufferStore`) with code of its own: `Prog::byte_to` and `byte_from` test the index and read the buffer's address off the layout, proved by `goes_byte_to`, `goes_byte_from`, `goes_loads`, `goes_stores` and `goes_byte_node` (`lib/native/native_compile_bytes.hthr`). A function's byte nodes go through the shared leaf (`emit_leaf`, `lib/native/function_ir/function_ir_lower_calls.hthr`), which takes a buffer's home as two values of its scope and lowers an access where the path knows the index below the length. This is step 5d of U5 ([[native-one-compiler]], `docs/native/native-procedures-are-functions-design.md` §3) and step V6 of the views ([[source-buffers-as-views]], `docs/native/native-library-exports-design.md` §3.1). It is the one place the two compilers still lower the same node twice.

## What it takes

Scoped on 2026-11-11 (the log of [[source-buffers-as-views]] has the entry in full):

- The leaf's theorems are stated in the function compiler's frame: what a leaf leaves is `Stack::Trail(lending, d, …)`, stores below offset `d + 64`, the 64 bytes at RSP being a function's spill slots. A statement's frame words sit there. No leaf stores to the stack, so the theorems (`kept_block_emits` through `emit_leaf_runs`) hold at any bound and are restated over a bound `i`, the `d` forms their instances.
- The statement side keeps its bound test and hands the access to the leaf with the home loaded as two immediates (`Layout::homes_block` loads them so for a callee). It then proves a byte node from the lending it already gives its callees (`Target::lending`, `loan`, `in_memory`, `based_left`), with a register file and a valuation built at the leaf.
- That bridge is longer than the two theorems it replaces. The machine fact shared is one MOVZX and one byte MOV.

## Why it waits

It pays when a statement holds a buffer's home as a word and not as a layout constant, which is a statement that lends a view itself ([[statement-lends-named-buffers]]). Both of the things the native work drives at (the lexer linked into Rust, a hash compiled and proved) read and write bytes in functions, through the leaf. So this is health and not a blocker: one lowering of a byte node, and `native_compile_bytes`' code gone.

## Done when

`native_compile_bytes.hthr` has no emitter of its own, `tr` and the tools that index a buffer compile to the bytes they compile to now or fewer, and their certificates check.

## What it assumes from elsewhere

- **[[statement-lends-named-buffers]]** decides what a statement's home is. Built before it, the bridge is written for literal addresses and again for words.
- **[[native-one-compiler]]** owns the order of U5's steps.
