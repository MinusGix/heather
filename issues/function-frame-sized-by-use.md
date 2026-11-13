---
title: Size a compiled function's frame by what it uses
status: open
labels: [native,x86,ir,proofs]
area: heather-in-heather
milestone: [hih-passes,nh-library]
created: 2026-11-12
updated: 2026-11-12
---

Every function the verified lowering emits opens a frame of 112 bytes: eight slots for the caller-saved registers a call stores round itself and six for the callee-saved registers a function may save (`frame_allocate`, `function_opened`, `lib/native/function_ir/function_ir_lower_calls.hthr`). The size is one constant so that the body's theorems speak of one depth. A leaf that saves nothing uses none of it ([[function-ir-verified-leaf-frame]] is that case), a caller that saves nothing uses 64 bytes, and only a function that saves all six uses the whole.

The cost is in the contract and not in the instructions: the stack an export states is 120 bytes for every function before it in its program (`120 * Succ(f) <= i` in `compiled_returns`). It was 72 before a function could save ([[function-ir-values-in-kept-registers]]). [[linked-program-entries-limits]] has the other half of the same figure: the bound counts a function's index, not what it calls.

## What it takes

- The frame as a function of the function: no slot for a leaf's calls, `8 * saves` for its saves, the saves directly above RSP in a leaf. The count is already threaded through the body's theorems (`saves`); whether a body calls is `StructuredRegion::calls`. `function_runs` takes the frame's size as it takes the count today, and the save slots' place (`Stack::saved_above`, slot 8 on) becomes the size of the spill area.
- The contract's room by function: a table of depths, a function's own frame and return address plus the deepest of the functions it calls, in place of `120 * Succ(f)`. `lower_program_correct` is already an induction over the program in that order, and `compile-x86` already writes a figure per export into the file's stack line (`Signature::stack`, `crates/cli/src/native.rs`).
- The statement compiler's bound (`128 * functions`, `native_compile_function.hthr`) follows the table.

## Done when

A leaf export that saves nothing states the eight bytes of its return address, and `scan_token`'s line is the sum of the frames on its deepest path.
