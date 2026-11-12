---
title: Values that live across a call belong in callee-saved registers
status: open
labels: [native,x86,ir,planner,proofs]
area: heather-in-heather
milestone: [hih-passes,nh-library]
created: 2026-11-12
updated: 2026-11-12
---

A function that calls plans its values in the caller-saved registers only (`call_pool`, `function_ir_lower_calls.hthr`), and every call spills all of them to the frame and reloads them ([[function-ir-verified-live-spills]] owns making that only the live ones). So a value that lives across a call costs a store and a load at each call, and a calling loop with five state words has three registers left in its body ([[function-ir-planner-register-pressure]], which was fixed without adding registers).

The callee-saved registers (RBX, RBP, R12 to R15) hold nothing in compiled functions today. The function contract already says a callee keeps them (`callee_kept`, `Kept` in `Stack::Closed`), so a value placed in one is still there after a call with no spill.

## What it takes

- The function's entry saves the kept registers it uses and its exit restores them, as a compiled procedure's entry and exit already do (`saves`, `restores`, `goes_saves`, `goes_restores`, `native_compile_perform.hthr`; U5 step 5b). The frame has the room computed from the count.
- `leaves_all(code, callee_saved())` becomes "leaves all but the ones saved", and the function's own `Kept` clause is proved from the save and restore, not from never writing.
- The planner: a value read after a call prefers a kept register; one that is not prefers a caller-saved one. A loop's state in kept registers needs no spill at the body's calls.

Smaller, and the planner's alone: a value whose only read is a move into an output should take the register that output is wanted in when it is free at the move (the second refusal of the planner issue was a value sitting where a later output was wanted; it was fixed by letting the last values of a pass stay in RAX, which does not help a value made before a call).

## Done when

`scan_token.s` keeps the loop's state across `scan_step`'s call with no store or load of it, and its stack line says less than it does now.
