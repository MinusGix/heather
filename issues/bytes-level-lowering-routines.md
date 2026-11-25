---
title: The bytes level's routines and calls lowered: one valuation per scope, function_runs_by, call_step_by, the done clause
status: open
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
