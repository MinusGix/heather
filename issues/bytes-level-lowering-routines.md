---
title: The bytes level's routines and calls lowered: one valuation per scope, function_runs_by, call_step_by, the done clause
status: closed
labels: [native,function-ir,x86,memory,ownership]
area: heather-in-heather
milestone: [nh-ownership]
created: 2026-11-25
updated: 2026-11-25
---

Items 4 and 6 of [[bytes-level-lowering]]: a routine's entry, exit and run, an ordinary call on values, and the done clause of `Site::Meets` for every routine of a program the lowering returns. Nodes, leaves, sequences and branches are lowered and proved in `lib/native/bytes_level/bytes_level_lower.hthr` (`Body::emit`, `Body::emit_emits`, at `EmitsBy` with state `Heap` and clause `heap_in`).

## Scope

- **One valuation per scope exists.** The theorems are over a FunctionIR valuation agreeing with the locals at every node (`Locals::Agrees`, `RunAgrees`). State the lowering's check that no id is bound twice in a scope (a routine's body; a loop's pass is its own), and prove that a run of a checked body determines a valuation agreeing with it everywhere (a frame lemma: a node, a region, a call's results change only the ids they bind), with the run's final locals lowered (`Value::lower`) as the witness. Then `run_instrs_holds` and its region form give the facts `Body::emit_emits` takes.
- **The routine**: parameters bound in the valuation as `lower_values` of the arguments (a reference as its address), the body's emission under `function_runs_by` at `Mem := heap_in` (cited; its `body_emits` is `Body::emit_emits` at the frame's state), the results moved to RAX and `answer_registers()` (`result_moves`).
- **A call** (`Body::Call`): FunctionIR's call code (`File::emit_call`) proved by `call_step_by`/`call_emits` at the instance, the callee's contract `Pre`, `Post` being the routine theorem at one fuel less (the induction over fuel that ties routines, as `program_calls` ties them).
- **The done clause** (`Site::MeetsDone`) for every routine, at every fuel.
- Small relocations noticed: `Site::moves_word_load` (written in the lowering module, the doubleword's lemma at eight bytes) belongs in `x86_64_stack_runs` beside `moves_dword_load`; `pure_emits` (a pure block as `EmitsBy` at any clause) belongs beside `kept_block_emits` in `function_ir_lower_calls`.

## Done when

`Site::MeetsDone` holds for each routine of every program the lowering returns, whatever the placement, for programs without loops or system calls; the language's call probes (`lend_*`, `both_*`) compiled with their theorems.

## What it assumes from elsewhere

- **[[bytes-level-lowering]]** owns the node, leaf, sequence and branch lowering. Assumed: `Body::emit_emits` as stated.
- **[[lowering-generic-in-memory]]** owns `function_runs_by`, `call_step_by`. Assumed: citable at `S := Heap`.

## Log

- 2026-11-25: Built (branch `claude/bytes-level-lowering-routines`). **Done clause proved for every routine of every program `Program::lower` returns, at every fuel, for programs without loops or system calls; `lend` and `both` compiled with their theorems.**

  - **One valuation per scope** (`lib/native/bytes_level/bytes_level_scope.hthr`). The check is `Body::fresh` (no id bound twice along any path: both arms of a branch may bind an id, nothing after the branch may bind it again). The frame is `Frames` (a checked run changes only the ids it binds), the invariant `Scoped` (a word id holds no reference beside it, a reference id one, and references only at ids the scope bound), the witness the final locals lowered (`Locals::lower`, `Locals::Shows`, `agrees_of`). `Body::holds_of` turns a checked run into the facts `Body::emit_emits` takes; `leaf_agrees` gives `run_instrs_holds` its `RunAgrees` unedited.
  - **A call** (`bytes_level_lower`): `File::emit_call` with no buffers, proved by `File::emit_call_steps_by` with each CALL by `call_step_by` at the heap's clause (`call_heap_step`, `call_heap_emits`); the callee's contract is `RoutinePre`/`RoutinePost`, its answer at the fuel the call was given (`run_answers`). `Body::Holds` gained the callees' answers and the `spare` id; `Body::emit_emits` gained `CalleesReturn` and FunctionIR's `CallFrame` framing (`Body::calls`, `Body::Fits`).
  - **The routine** (`bytes_level_routines`): `routine_runs` is `function_runs_by` at the heap's clause around `Body::emit_emits`; `routine_body`/`routine_closes`/`routine_returns` the frame arithmetic and `Site::returns_by`, as FunctionIR's `function_body`. A routine with no results answers zero in RAX from an id its scope never binds (`ids_past`), since FunctionIR's call and function theorems have a word in RAX; `Site::Returned` says nothing of RAX then.
  - **The program**: `emit_routines` at labels `1` on, `routine_rooms` (largest frame over the callees' rooms), `Program::lower` (checks validity and layout). `program_returns` is the one induction on fuel: at `n + 1` a routine's calls are answered at `n` and met by the hypothesis. `program_quiet`: a done run with no system call keeps its world. `lower_program_meets_done`: `Site::MeetsDone`.
  - **Refused**: a routine calling itself or one above it (`Site::Entering`'s room is fixed for every fuel; the meaning ties recursion by fuel, so its depth is unbounded), and a scope binding an id twice. Probes and controls in `lib/_tests/native/bytes_level/bytes_level_routines_tests.hthr` (`lend_lowers`, `lend_meets_done`, `both_lowers`, `both_meets_done`, `self_call_refused`, `twice_refused`, `arms_fresh`, `after_arms_refused`).
  - **Relocated**: `Site::moves_word_load` to `x86_64_stack_runs` beside `moves_dword_load`; `pure_emits` to `function_ir_lower_calls` beside the `EmitsBy` definitions (after them, as it uses them).
  - **Cited as stated**: `function_runs_by`, `call_step_by`, `File::emit_call_steps_by`, `may_emit_by_seq`, `branch_emits_by`, `Site::returns_by`, `label_target`. None needed more than its statement.
  - **Cost** (uncached, width one): `bytes_level_scope` 93 items 0.5 s; `bytes_level_routines` 97 items 2.4 s, 1.2M steps (dearest `Program::lower` and `routine_body`, each under 0.4 s; `routine_body` first ran out of fuel as one theorem and was split into `routine_body` and `routine_closes`); `bytes_level_lower` 123 items 4.0 s (dearest the emitters' definitions and `call_heap_step`, under 0.5 s each); probes 0.1 s.
  - Verified: `scripts/linked --check` every export unchanged; `HEATHER_PR_NATIVE=all scripts/test --pr`: `== suite: 4139 passed, 0 failed, 3 ignored ==`.
- 2026-11-25: Filed after closing, at the coordinator's request: [[generic-call-empty-answer]] (the zero in RAX for a routine with no results, to be removed at the generic theorems' source) and [[bytes-level-lowering-recursion]] (recursion refused; the room by call depth).
