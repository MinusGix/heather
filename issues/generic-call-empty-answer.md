---
title: function_runs_by and call_step_by at an empty answer: no word forced into RAX
status: open
labels: [native,function-ir,ownership]
area: heather-in-heather
milestone: [nh-ownership]
created: 2026-11-25
updated: 2026-11-25
---

`function_runs_by`, `call_step_by`, `File::emit_call_steps_by` and `call_emits` (`lib/native/function_ir/function_ir_lower_calls.hthr`) carry exactly one word in RAX: a function's `result: Nat` moved there (`result_moves`, `Stack::ClosedBy`'s `Answered(answer, rest, ·)`), a call's `result` held there after it (`File::called`, `Stack::CalledBy`). A routine that answers no words has none, so the bytes level's lowering (`lib/native/bytes_level/bytes_level_routines.hthr`) makes one: a routine with no results answers zero in RAX from an id its scope never binds (`answer_instrs`, `ids_past`), and a call with no results lands that zero at the same spare id (`call_result`, `answer_head`). That is one instruction per such return, and a contract stronger than `Site::Returned` (which says nothing of RAX for an empty answer), existing only because of the generic statements.

## Scope

- State the answer as a list of words in `Cons(Rax, answer_registers())` (`ArgsIn`, as `Site::Returned` does) in `Stack::ClosedBy`, `Stack::CalledBy`, `result_moves`, `File::called`, with the one-word form FunctionIR uses its instance (no certificate changes).
- Then remove `answer_instrs`, `answer_head`'s zero and the spare id's call landing from the bytes level's lowering.

## Done when

A routine with no results compiles to no answer instruction, and `lend`/`both` (`lib/_tests/native/bytes_level/bytes_level_routines_tests.hthr`) keep their theorems.
