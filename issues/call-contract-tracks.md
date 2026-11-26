---
title: The call contract tracked on fuel: claims with lower bounds, Site::Tracks, room by call depth
status: open
labels: [native,x86,linux,ownership]
area: heather-in-heather
milestone: [nh-ownership]
created: 2026-11-25
updated: 2026-11-26
---

The coordinator's round on the call contract (docs/language/ownership-design.md §17.7): the contract tracked on fuel. Three things were wrong with `Site::Meets` (`lib/std/arch/x86_64/x86_64_call_contract.hthr`) and are fixed together: its going clause is a universal over every reachable state, which no region theorem proves; the generic region theorems are over `Site::Moves`, so a region holding a system call cannot cite them; and a routine's room is fixed for every fuel, so recursion cannot be stated.

## Scope, in order (each landed and pushed before the next)

- **A.** Fuel is spent where the machine takes a counted step: a loop's first pass at the loop's own fuel, each turn back costs one; a call costs one. `Site::Performs` gains a lower bound `least` on machine steps, with its bind (counts and bounds add).
- **B.** The generic theorems in claim form (`EmitsBy`, `may_emit_by_seq`, `branch_emits_by`, `call_step_by`, `File::emit_call_steps_by`, `function_runs_by`, `Site::loop_iterates`, `Site::Returns`), their present statements instances at no system call and bound zero; every certificate unchanged.
- **C.** `Site::Tracks` (for every fuel, the code performs the goal read off the meaning: done, exited, going with the lower bound, stuck nothing); `MeetsDone` and `MeetsExited` as its readings; room by routine and call depth (`room(f, peak)`); the lending law inside `Site::Entering`, `io.Answerable()` only where used; the lowering re-proved to `Tracks`; recursion admitted with a probe and a control.
- **D.** `MeetsGoing` restated with the stuck alternative, and `Tracks → Meets` proved once, by determinism between system calls.
- **E.** Only if A to D land: the `Sys` node and `Exit`.

## Done when

A to D landed with `scripts/linked --check` unchanged and `HEATHER_PR_NATIVE=all scripts/test --pr` green at each; §17.7 written; E landed or what remains of it stated exactly.

## What it assumes from elsewhere

- **[[bytes-level-lowering-world]]**'s last log entry is the design ground (the coordinator's six questions).
- **[[bytes-level-lowering-recursion]]** stays open for the out-of-room outcome (the old compiler's exit 139), which this round does not give a meaning.

## Log

- 2026-11-25: **A landed** (items 1 and 2). Fuel is spent where the machine takes a counted step: `loop_run` is `loop_pass` at the loop's own fuel then `loop_later`, whose `Succ` case is the turn back (`bytes_level.hthr`); a call costs one as before. Termination stays structural (`loop_later` recurses on fuel, `loop_pass` takes what follows as an argument). Re-proved over the three: `loop_run_below` (fuel), `_canonical`, `_renames`, `loop_run_io`, `loop_run_no_exit` (routines) and `loop_holds_of` (scope: now `PassesHold` at `Succ(fuel)`, one pass more than the fuel), each as a pass lemma, a `later` induction and the run. Probes: `countdown(3)` is going at fuel 2 and done at 3 (was 3 and 4); new `countdown_one_pass` (one pass done at the call's fuel alone).

    `Site::Performs` carries `least` and moved to `x86_64_stack_runs`, generic over a world type and a `Kernel<M, W>` (what a system call does: `resumes` with its monotonicity), because the generic theorems' modules cannot import the Linux world (hand-listed module sets in `crates/elab/tests`) nor the contract (its `Answer`/`Value` collide with FunctionIR's). The contract's Linux step is its one instance, `Site::linux_kernel`; `Site::LinuxPerforms` is the claim there. Lemmas, once: `performs_less`, `performs_up`, `performs_more`, `performs_weaken`, `performs_prefix` (counted steps before), `performs_after` (uncounted steps before), `performs_steps` (a machine run is a claim at bound zero), and `performs_bind` (counts and bounds add; calls as `calls2 + calls` so a first claim at none reduces). Probes: `linux_bind` and the control `steps_not_counted` (uncounted steps do not give bound one) in `x86_64_call_contract_tests`.

    Deviation reported to the coordinator: at the top the going bound is `n - 1`, not `n` — the first CALL of the chain is the caller's instruction, before `Site::Entering`'s state.

    Verified (tree at the A commit): `scripts/linked --check` every export unchanged; `HEATHER_PR_NATIVE=all scripts/test --pr`: `== suite: 4139 passed, 0 failed, 3 ignored ==`.
- 2026-11-26: **B landed** (item 5). The generic theorems are stated once, in claim form (`Site::Claims` at a `Kernel<M, W>`, a world clause `World: S → W → Type`, at most `calls` system calls and at least `least` machine steps), and their former statements are one-line instances at the quiet kernel (`Kernel::none`), the world `True`, no system call and bound zero: `EmitsBy`/`MayEmitBy` (of `EmitsClaim`/`MayEmitClaim`, `emits_of_claim`/`may_emit_of_claim`), `may_emit_by_seq` (of `may_emit_claim_seq`), `branch_emits_by` (of `branch_emits_claim`), `call_step_by` (of `call_step_claim`), `File::emit_call_steps_by` (of `File::emit_call_steps_claim`), `function_runs_by` (of `function_runs_claim`), `Site::loop_iterates` (of `Site::loop_iterates_claim`), `loop_body_runs_by` (of `loop_body_runs_claim`) and `Site::returns_by` (of `ReturnsClaim` via `returns_claim_of`/`returns_by_claim`, `Site::returns_of_quiet`). `Site::moves_test_by` is re-proved through `test_by_steps`. The stack-runs side gained, once: `Kernel::none`, `Arrived`, `Claims`, `claims_of_moves`/`moves_of_claims`, `claims_trans`, `claims_weaken`, `claims_carry`, `claims_loosen`, `claims_absurd`, `claims_jump_item` and `claims_call` (each the one counted step: a JMP back, a CALL), `claims_then`, `claims_after_moves`, `claims_test_by`, `claims_branch_by`, `performs_none`, `moves_of_quiet`, `returns_of_quiet`. Deleted as duplicates: `call_returns`, `call_emits`, `function_runs_saved` (now `function_runs_saved_claim`).

      The two kernel-write facts the claims need are in the contract module, from the Loan (`Spans::Window`, `Site::window_keeps_code`, `Site::resumes_resident`); no `ClauseStable` law for kernel writes was added (one instance needs it). Probes: `heap_call_step_claim` and `plain_loop_counted` (`function_ir_lower_calls_tests`: a CALL and a loop's turn counted), `linux_bind` and the control `steps_not_counted` (`x86_64_call_contract_tests`).

      Every certificate unchanged: `scripts/linked --check` exit 0, the 20 exports unchanged. Verified: `HEATHER_PR_NATIVE=all scripts/test --pr`: `== suite: 4139 passed, 0 failed, 3 ignored ==`.
