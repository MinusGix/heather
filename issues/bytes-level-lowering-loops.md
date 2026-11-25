---
title: The bytes level's plain loop lowered by Site::loop_iterates on fuel
status: closed
labels: [native,function-ir,x86,ownership]
area: heather-in-heather
milestone: [nh-ownership]
created: 2026-11-25
updated: 2026-11-25
---

Item 5 of [[bytes-level-lowering]]: the plain loop (`Body::Loop`), by `Site::loop_iterates` on the run's fuel with the counter-free head `Stack::LoopAt` and `loop_turns`, `loop_body_runs_by` at `Mem := heap_in` (`lib/native/bytes_level/bytes_level_lower.hthr`). A pass has its own valuation (its locals start empty), so the head carries the state as words in registers, a reference as its address, which `Stack::LoopAt` already states over any words.

## Done when

`Body::emit` lowers a loop and `Body::emit_emits` covers it; the language's `countdown` probe compiled with its theorem.

## What it assumes from elsewhere

- **[[bytes-level-lowering-routines]]** owns the scope valuation's existence. Assumed: a pass's run determines its valuation as a routine's does.

## Log

- 2026-11-25: Built (branch `claude/bytes-level-lowering-routines`). **`Body::emit` lowers the plain loop and `Body::emit_emits` covers it; `countdown` compiled with the done clause (`countdown_meets_done`).**

  - **Meaning at the valuation**: `PassesHold` (bytes_level_lower): the loop's passes at some fuel, each at a valuation of its own (a pass is its own scope from its parameters), its body's facts from the heap it starts at to the one it leaves, the exit bit ending with the next words or going round at one fuel less; nothing ends at no fuel. `Body::Holds(Loop)` is `PassesHold` at some fuel from the inputs' words to the outputs'.
  - **Code**: the inputs moved into the state's registers (one `Into` place each, `state_registers`; `File::plain_entry`), head H, the pass from the file holding only the parameters, the exit bit's `File::branch_test` with a jump to C where clear, the next words moved in and JMP J, at C the same moves and JMP H, then J (`plain_done`; labels `names + 1..3`, the pass's from `names + 4`). The file after has the outputs in the state's registers.
  - **Proof**: `plain_passes` is `Site::loop_iterates` at `S := Heap` on the fuel, the head `Stack::LoopAt` (`PlainAt`), each pass `loop_body_runs_by` at `heap_in` (`plain_step`), the turn `loop_turns` then JMP H (`plain_turns`), and the leave its own (`plain_leaves`: the bounded loop's `loop_leaves` has its flag in it). All cited as stated; none needed more than its statement. `plain_loop_emits` adds the entry and the file at J.
  - **The bridge**: `Body::fresh(Loop)` checks the pass as a scope of its own and counts its ids bound in the routine's scope too, so the routine's spare id is none of a pass's (each pass valuation is zero there) and nothing after the loop rebinds one (control `countdown_reusing_refused`). `loop_holds_of`, by induction on the loop's fuel, gives `PassesHold` from the run, each pass's facts from `pass_close` (the pass's final locals lowered); `loop_scopes` frames the outer scope. `Body::holds_of` now also takes that the spare id is unbound in the scope (`Mem(spare, used2) → False`).
  - **Quiet**: `loop_run_io` (a loop of quiet passes keeps the world).
  - **Cost** (uncached, width one): `bytes_level_lower` 147 items 5.5 s (dearest `Emitted::plain_close` 0.8 s, evaluating `branch_test` and the moves); `bytes_level_scope` 107 items 1.1 s (`loop_holds_of` 0.39 s); `bytes_level_routines` 3.0 s (`loop_run_io` 0.33 s); probes 0.2 s.
  - Verified: `scripts/linked --check` every export unchanged; `HEATHER_PR_NATIVE=all scripts/test --pr`: `== suite: 4139 passed, 0 failed, 3 ignored ==`.
