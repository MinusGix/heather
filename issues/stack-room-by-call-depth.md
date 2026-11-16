---
title: Ask a compiled function for the stack its calls need, not 136 bytes per function before it
status: open
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
