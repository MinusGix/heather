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

`scan_token.s` keeps the loop's state across `scan_step`'s call with no store or load of it.

Amended 2026-11-12: the first two bullets of what it takes are built (the log has how). What is left is the planner's preference, which waits on [[function-ir-verified-live-spills]]; the stack line, which this round made longer, is [[function-frame-sized-by-use]]'s.

## Log

- 2026-11-12: A second customer, with no call in it: a loop over two lent spans (`differ_from`, `lib/_tests/native/runtime/runtime_lent_tests.hthr`, [[runtime-loop-over-several-spans]]). A lent span's home is two words kept in place through a loop, so two spans and the loop's count leave a body four of the nine caller-saved registers. The loop that makes its next index before it reads its two bytes has nine values live at the second load (four home words, the index, the sum, the next index, the count, the first byte) and the load's word is a tenth. The same loop with the sum's parameter before the index's compiles. So the kept registers are wanted for a function's long-lived words whether or not it calls: home words and a loop's count are read all through the body and never written, which is what a kept register is for. SHA-256's compression over a state span and a block span will have more live words than this.

  A smaller step that would also have fitted this loop: the loop's count in a frame word, since it is read once a pass.
- 2026-11-12: A third customer, and the one that blocks something: a loop that lends ([[source-buffers-as-views]], `each_body` in `lib/_tests/native/runtime/rt_file_lend_tests.hthr`). A pass lends a window of each of two spans to a callee and goes round. It lowers from the file layer and runs, and the function compiler refuses it:

      in a loop's pass, …, the call of function 0 (22, 23, 24, 25, 19): an argument is in no register, where rax holds 25; rcx holds 9; rdx holds 8; rsi holds 7; rdi holds 6; r8 holds 10; r9 holds 15; r10 holds 11; r11 holds 19;

  Twelve values are wanted at the call: the four kept home words (6 to 9), the index and the next index (10, 15), the loop's count (11), the argument (19) and the four words the views bind (22 to 25). Nine registers hold a function's values, so the first three view words are overwritten before the call that takes them. Nothing in the planner can fix this: every one of the twelve is read at or after the call. The probe pins the refusal (`each_refused`, `each_refused_why`) and has to change when this is built.

  With the six kept registers the same pass fits: the four home words, the count and the next index are read across the call and never written in the pass, which leaves the nine caller-saved registers for the index, the argument and the four view words. SHA-256's loop over its blocks is this shape with a state span written and a block window read, so views for the hash wait on this issue. A view of a whole buffer (from the constant 0 to its length) also binds two fresh words that are copies of its home; handing the home's own registers on would save two more, in `File::emit_lend` and its theorem.
- 2026-11-12: Built, as capacity. A function's placement begins by saying how many callee-saved registers the function saves (`Saving(count)`, a prefix of R12, R13, R14, R15, RBX, RBP; no head means none, so a placement written before means what it did). The function stores them above its eight spill slots at its entry and loads them back before its return (`function_opened`, `function_closed`, `function_ir_lower_calls.hthr`). The body is checked to leave RSP and the registers the count does not cover (`body_kept(saves)` where each leaf had `callee_saved()`; the count is threaded through the body's emitters and theorems), and `function_runs` proves the caller's `Kept(callee_kept())` from the body's invariant and the loads (`saves_restored`, `Stack::saved_above`: the save slots are above the body's trail, so `Loan::unchanged` says they are as the entry left them). After a call the body's invariant is rebuilt from the callee's contract (`body_kept_of`), so a value in a saved register is read after a call with no store of its own. The planner's pool is the caller-saved registers and then `kept_order()`; it takes a callee-saved register only when the others all hold live values, and writes the count only then (`places_saving`).

    The two customers that were refused lower with the planner's placement: the loop that lends with three saved and its machine-level theorem (`each_carries`, `rt_file_lend_tests.hthr`), and `differ_from` with one (`differ_from_lowers`). Both refusal probes became lowering probes, with the same places and no count as their control. `lib/_tests/native/function_ir/function_ir_saves_tests.hthr` pins a leaf and a caller to their instructions with a value in R12, and refuses no count, a register past the count and a count where a node's place is read. The refusal report says when a place is a callee-saved register the count does not cover (`Place::unsaved`).

    What it did not do, against the done-when as it was written:

    - Nothing is stored less. A call still spills all eight caller-saved registers, and the planner does not prefer a saved register for a value read after a call: with every register stored round the call anyway, the preference would cost a save pair and buy nothing. It pays once [[function-ir-verified-live-spills]] is built, and the preference is then what is left of this issue.
    - The stack line says more. Every frame is 112 bytes whatever the function saves, so the bound an export states went from 72 to 120 bytes a level ([[function-frame-sized-by-use]]).
    - One plan that lowered before is dearer. A node's value takes a saved register only after what costs nothing (`Node::fresh`: a free caller-saved register, then RAX or the register of an operand that dies at the node, as before), so ten of the eleven export files differ in the frame's size alone. A branch's meeting register and a loop's registers used to fall back on RAX with the pool full and hope (`pick_targets`, `File::free_or_rax`); they take a saved register now, which is right in principle, since RAX does not live across a call, and is one function of `scan_token`'s thirty-four, 13 bytes longer. Trying a saved register before RAX and a dying operand grew four exports, which is why the order is this one. None of it is measured in time.
  - The count is a prefix of one order, so a function is never asked to save RBX alone. The planner takes them in that order, so it costs nothing today.
