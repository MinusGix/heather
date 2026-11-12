---
title: A function's buffer homes hold registers to its end, and a lend of two views runs out
status: open
labels: [native,ir,x86,planner]
area: heather-in-heather
milestone: [nh-library]
created: 2026-11-12
updated: 2026-11-12
---

Found writing the probes of a call over views (`lib/_tests/native/function_ir/function_ir_lower_views_tests.hthr`, [[native-library-exports-design]] §3.1). A function lent two buffers that lends two views and passes one more word, with one view from the constant 0, is refused:

    the call of function 0 (11, 12, 13, 14, 5): an argument is in no register, where rax holds 14; rcx holds 3; rdx holds 2; rsi holds 1; rdi holds 0; r8 holds 13; r9 holds 5; r10 holds 6; r11 holds 11;

Value 12, the first view's length, was computed and then overwritten. Nine registers are in play (the scratch pool with RAX), and the body wanted ten values at once: the function's four home words (0 to 3), the argument 5, the constant 6, and the four words the views bind (11 to 14).

The four home words are the cause. A function's homes are planned as live to the function's end (`Function::kept`, `lib/native/function_ir/function_ir_lower_calls.hthr`: a load reads its home's base, "which no node says"), so they hold four registers through a lend that is the last thing to read them, and through everything after it. The report above was read a register at a time, for want of a command that prints a term's value ([[eval-command-for-closed-terms]]). The probe was rewritten to want fewer (`crossing` passes `mid` as the index, `renames` lends one view), which is what a hand would do and a generator cannot.

## Ways

- **Liveness of homes by position.** `StructuredRegion::home_reads` already lists the home ids a region reads. Planning a home as read at each load, store and view of its buffer, as an operand is, frees it after the last one. The planner is untrusted search: no theorem moves, and the lowering still refuses a plan that lost a home a later leaf needs.
- **Spilling.** A function has eight frame slots, used only around calls. A value that is live across a stretch with no free register could be kept in a slot ([[function-ir-planner-register-pressure]] names this as the general fix and did not need it). This is the lowering's and its theorem's, not only the planner's.

The first is small and covers this shape; the second is what a longer body will want. [[planner-branch-output-from-call]] is the other planner gap the same probes met.

## Done when

The `crossing` of the first draft (two views, one from the constant 0, and an index of its own; the shape is in this issue's first paragraph) lowers in `function_ir_lower_views_tests.hthr`, and `scripts/linked --check` shows no generated file moved.
