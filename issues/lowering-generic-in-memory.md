---
title: The lowering's frame, call and loop theorems generic in their memory clause, with the old statements as an instance
status: open
labels: [native,function-ir,memory,ownership]
area: heather-in-heather
milestone: [nh-ownership]
created: 2026-11-25
updated: 2026-11-25
---

Stage 2 of `docs/language/ownership-design.md` §17.5: the existing lowering's frame, call and loop theorems made generic in what they say about memory, so the new memory layer cites them instead of restating them.

[[bytes-level-language]]'s reading (its log has the table, theorem by theorem): in `lib/native/function_ir/function_ir_lower_calls.hthr`, about 170 theorems are words and frame only; 8 are already generic in `keep: M → Type` (`epilogue_moves`, `result_moves`, `loop_rounds`, `loop_stops`, `loop_enters`, `loop_marks`, `loop_leaves`, `epilogue_moves_words`); and about 90 more go through `EmitsOver`, whose `Stack::Trail(…, now: Buffers())` they use only for stability under the frame's own stores (the call sequence, `call_step`, `Site::loop_passes`, `loop_emits`, `function_enters`, `function_closes`, `function_runs`, `program_step`). Without a generalisation the new lowering restates roughly that many lines.

## Scope

- **A memory clause.** `EmitsOver`, `ArgsReady`, `Called`, `Entered` and `Closed` take `Mem: S → M → Type` with one law, that it is stable under the frame's own stores (`(now) → stack.Stable(w, Mem(now))`), and `Site::loop_passes` ranges over a state type. Each of the ninety is then proved once, generically.
- **The old instance.** The existing statements are the instance at `Buffers()` and `Stack::Trail`, as abbreviations with one-line derivations, so every existing caller and every existing certificate is unchanged.
- **The new instance stated**, as a probe that the clause holds at "the stores were inside the lending and the heap is injected" (`WroteIn ∧ Injected` of `lib/std/arch/x86_64/x86_64_memory_contract.hthr`), so [[bytes-level-lowering]] cites the generic theorems at it.
- **Loops without a bound**: the reading's second table says which loop theorems survive as they are, which survive with the counter cut out (`loop_entry_sound`, `loop_rounds`), and that `Site::loop_passes` becomes an induction on the run's fuel. State the generic forms so that both the bounded loop of the old lowering and the plain loop of the new are instances; do not remove the bounded loop here.

## Done when

The generic theorems and the old instance pass the suite with every existing certificate unchanged (`scripts/linked --check`, the native gates), the new instance's probe checks, the cost of checking `function_ir_lower_calls` is reported before and after, and the log lists each theorem made generic.

## What it assumes from elsewhere

- **[[x86-memory-contract]]** (closed) gives `WroteIn`, `Injected`, `Stable`.
- **[[bytes-level-on-the-contract]]** is moving the language onto the contract's heap at the same time; this issue touches `lib/native/function_ir` and it does not.

## Log

- 2026-11-25: Round 1 (branch `claude/lowering-generic-in-memory`): **the frame, call, loop and function theorems of `function_ir_lower_calls` are stated once over a memory clause, FunctionIR's statements are its instance at the file, and the bytes level's clause is probed. No certificate changed.**

  **The clause and its law.** `Stack::TrailBy(spans, Mem, d, entry, now, memory) = WroteIn(d, spans, entry, memory) ∧ Mem(now, memory)` for any `Mem: S → M → Type`; the stores half stays fixed, since `WroteIn` is the contract's in both layers. The law is `Stack::ClauseStable(top, Mem) = (now: S) → stack.Stable(top, Mem(now))`, used directly only by `Stack::trail_by_store`. FunctionIR's instance is `S := Buffers()`, `Mem := Stack::FileIn(lending)` (`InMemory`), law `Stack::file_in_stable` (from `stable_in_memory`). The bytes level's is `S := Heap`, `Mem := Injected(spans, ·, ·)`, law `Loan::stable_injected`: `heap_in_stable` in `lib/_tests/native/function_ir/function_ir_lower_calls_tests.hthr`, with `heap_trail_store`, `heap_call_step` (`call_step_by` at it) and `plain_loop_on_fuel` (`Site::loop_iterates` at it on fuel), and a control (`heap_in_other_stable`, a clause over spans the loan does not lend, refused by the kernel).

  **Made generic** (generic name ← the old statement, now a one-line instance where the old region theorem still cites it; "in place" where only generic theorems cited it, so the old statement is gone):

  | Generic | Old statement | How |
  |---|---|---|
  | `Stack::TrailBy`, `Stack::TrailedBy`, `Stack::trail_by_store` | `Stack::Trail`, `Stack::Trailed`, `Stack::trail_store` | instances |
  | — | `Stack::Entered`, `Stack::entered_store` | deleted: `Entered` was `Trail` under another name |
  | `EmitsBy`, `MayEmitBy` | `EmitsOver`, `MayEmitOver` | instances |
  | `emits_by_weaken`, `may_emit_by_weaken`, `may_emit_by_seq`, `may_emit_by_still`, `emits_by_at`, `may_emit_by_some` | the `_over` names | instances |
  | `emits_by_seq`, `emits_by_still`, `emits_by_some` | `emits_over_seq`, `_still`, `_some` | in place (cited only by the `may_` forms) |
  | `branch_emits_by` | `branch_emits_over` | instance; the facts are any `Holds`, `Yes`, `No` with the two picks, FunctionIR's the region's meaning (`when_nonzero_over`, `when_zero_over`) |
  | `Stack::StagedBy`, `Stack::ReturnedBy` | `Stack::Staged`, `Stack::Returned` | in place |
  | `Stack::ArgsReadyBy`, `Stack::CalledBy` | `Stack::ArgsReady`, `Stack::Called` | instances (cited by `lend_step`, `File::emit_call_runs`) |
  | `call_step_by` | `call_step` | instance; see below |
  | `call_spills`, `call_stages`, `call_moves`, `call_raises`, `call_returns`, `call_finishes`, `call_emits`, `File::emit_call_staged_steps`, `File::emit_call_saving_steps` | same | in place |
  | `File::emit_call_steps_by` | `File::emit_call_steps` | instance |
  | `Stack::ClosedBy` | `Stack::Closed` | instance |
  | `function_enters`, `function_closes` | same | in place |
  | `function_runs_saved` | same | in place; the body's emission is a hypothesis (`body_emits`) rather than proved by `emit_calls_runs`, and the function's `Function` fields are its result, extra words and parameters |
  | `function_runs_by` | `function_runs` | instance; `body_emits` from `emit_calls_runs` at the frame's state |
  | `Site::loop_iterates` | `Site::loop_passes` | instance; see the loops |
  | `Stack::LoopAt`, `loop_body_runs_by` | `loop_body_runs` | instance (the counter one more register) |
  | `loop_turns` | `loop_rounds` | `loop_rounds` is `loop_turns`, the counter's step and the jump |

  **Stayed FunctionIR's, citing the instances**, each with the file in its statement for a reason of its own: `may_emit_over_of_in` (a leaf proved over `LentAll`, `in_memory_lent`), `store_emits`, `wide_store_emits`, `emit_leaf_runs`, `lend_step`, `File::emit_lend_runs`, `File::emit_call_runs`, `StructuredRegion::emit_calls_runs` (the region's relational meaning over `Buffers()`), `loop_emits` and `loop_close_emits` (the bounded `LoopRunsOver` over `Buffers()`, composed now from `loop_iterates`, `loop_body_runs_by` and `loop_turns`), `program_step`, `lower_program_*`, `may_emit_over_bound` (one `j`).

  **What used more than stability.** Two things, neither of `Mem`. (1) The CALL relates the callee's clause to its caller's. It was already two hypotheses over an abstract `inner` lending; `call_step_by` takes the callee's contract as any `Pre`, `Post` (what `Site::moves_call` takes), with `enters` (the words passed and `Mem(before)` give `Pre`) and `leaves` (`Post` gives the answer, the kept registers, `WroteIn` over the caller's spans and `Mem(after)`). FunctionIR's instance fills them from `CalledOver`, `AnsweredBoth` and its old `enters`, `leaves`. (2) The saved registers' slots survive the callee's stores and the body's by the frame rule under a `Loan` over the spans (`Loan::stable_saved`), so `call_step_by`, `function_closes`, `function_runs_saved` and `function_runs_by` take the loan beside the clause; both layers have one. No theorem used `InMemory` itself.

  **Loops.** `Site::loop_iterates` is the passes by induction on any `n` with `Runs(n, state, now)`: at zero `stop`, at `n + 1` a pass leaves or goes round to `Runs(n, …)`. A plain loop runs it on the run's fuel (`Runs(0, …)` is empty: `plain_loop_on_fuel`); `Site::loop_passes`, the bounded loop's, is it at `Runs := r < 2^64 ∧ LoopRunsOver(…, r, …)`, the counter's facts (`counted`, the exit bit) its step, with its old statement. A head is `Stack::LoopAt(keep, registers, words)`; the bounded loop's `LoopHead` is it with the counter as the first register and the passes left as the first word, which is how `loop_body_runs` and `loop_rounds` derive from `loop_body_runs_by` and `loop_turns` (from a pass, the exit bit clear: the jump to C and its moves of any ids into any registers). As the reading's second table has it: `loop_leaves` and `loop_exit_*` survive as they were (already generic in `keep`); `loop_entry_*`'s counter-free content is `moves_into`, already over any ids and registers, `LoopEntryOk` being it at `Cons(limit, inputs)`, `Cons(counter, state)`, so no new theorem; `loop_stops`, `loop_enters`, `loop_marks`, `loop_counter_*` are the bound's and stay until stage 3. `LoopRunsOver` stays over `Buffers()` (the bounded meaning goes with stage 3), so `loop_emits` is not generic in the state; the plain loop's is the new lowering's, from the same pieces.

  **Tier names.** The generic proofs now cite the contract for their own stores (`Stack::wrote_in_word`, `Stack::wrote_in_widen` at `Spans::within_self`) instead of `Wrote`, `wrote_store`, `wrote_in_own`, `wrote_in_deeper`. One remains through the stack: `call_step_by` keeps the passed words through `Stack::passes_unchanged`, which takes the tiers' `Stack::Unchanged` (filed: [[stack-unchanged-out-of-tiers]]).

  **Cost** (fresh cache, kernel gate at width one, the same binary; `--timings` over the module's own items). Module's own items, before → after: kernel evaluation steps 10,376,195 → 10,219,827 (−1.5%), reduce steps 9,763,429 → 9,823,137 (+0.6%), items 533 → 556; seconds within the run-to-run spread (the check is dominated by its imports). Per item: `call_step` 619k steps → `call_step_by` 359k + its instance 223k (the instance is the conversion of the old statement against the generic one); `function_runs` 209k → `function_runs_by` 163k + instance 60k; no generic proof is dearer than the one it replaced.

  **Verified**: `scripts/linked --check`: every export unchanged (compiled), no file rewritten. `HEATHER_PR_NATIVE=all scripts/test --pr` on the final tree (merged with the coordinator's `f268505`): `== suite: 4139 passed, 0 failed, 3 ignored ==`.
