---
title: Ask a compiled function for the stack its calls need, not 136 bytes per function before it
status: closed
labels: [native,theorems,exports]
area: heather-in-heather
milestone: [nh-library]
created: 2026-11-16
updated: 2026-11-16
---

`stack_room(f) = 136 * Succ(f)` (the premise of `compiled_returns`, named in `function_ir_correct.hthr`) charges a function for every function before it in the program, because a function may call only earlier ones. `scan_accept`, a few instructions, asks for 3,944 bytes in `crates/linked/generated/exports.rs`.

Wanted: the room by call depth, a table computed from the program and checked by evaluation, threaded through the lowering's proof as the premise. This changes the premise of a proved theorem, so the design goes to Minus first.

## What it assumes from elsewhere
- **[[linked-program-entries-limits]]** ("The stack bound by index") and **[[function-frame-sized-by-use]]** own the analysis so far. Assumed here only that the bound is by the call graph.

## Log

- 2026-11-16: Built. `program_depths` (function_ir_lower_calls) computes each function's depth, one more than its deepest callee's, and `lower_program_lent` refuses a program whose calls do not respect it (`program_shallow`, by evaluation). The contracts (`Stack::CalleePre`, `CalledOver`, `EnteredOver`, `Site::Calls*`) take a depth table `depth: Nat → Nat` and ask `136 * Succ(depth(f))`; the region proof carries `StructuredRegion::Shallow` (a call below the index bound is of a function less deep than the level). The statement compiler keeps the index as its table (`program_shallow_index`, no check needed). `Prog::Returns`/`Computes`/`ReturnsOver`/`ComputesOver` take the room, and `compiler_correct` states it as `stack_room(functions, f)`; certificates state the number. `STACK:` in `crates/linked/generated/exports.rs`: `scan_accept` 3,944 → 136, `scan_step` 3,672 → 408, `scan_begin` 4,896 → 136, `scan_token` 5,032 → 680, `List::scan_tokens` 6,120 → 816, `Sha256::compress` 3,672 → 1,088, `update`/`finish` → 1,496, `sha512_*` 408 → 272. What is left is the level's size by the frame a function uses: [[function-frame-sized-by-use]].
