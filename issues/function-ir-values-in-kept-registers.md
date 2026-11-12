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

## Log

- 2026-11-12: A second customer, with no call in it: a loop over two lent spans (`differ_from`, `lib/_tests/native/runtime/runtime_lent_tests.hthr`, [[runtime-loop-over-several-spans]]). A lent span's home is two words kept in place through a loop, so two spans and the loop's count leave a body four of the nine caller-saved registers. The loop that makes its next index before it reads its two bytes has nine values live at the second load (four home words, the index, the sum, the next index, the count, the first byte) and the load's word is a tenth. The same loop with the sum's parameter before the index's compiles. So the kept registers are wanted for a function's long-lived words whether or not it calls: home words and a loop's count are read all through the body and never written, which is what a kept register is for. SHA-256's compression over a state span and a block span will have more live words than this.

  A smaller step that would also have fitted this loop: the loop's count in a frame word, since it is read once a pass.
