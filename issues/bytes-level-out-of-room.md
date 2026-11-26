---
title: The bytes level's out-of-room stop: guards at calls into a cycle, one alternative in the contract
status: open
labels: [native,x86,ownership]
area: heather-in-heather
milestone: [nh-ownership]
created: 2026-11-26
updated: 2026-11-26
---

The bytes level's lowering tracks the meaning only under `room(f, peak(n, …)) <= i` (`Site::Entering`), and its code is unguarded: a recursion deeper than its stack has no defined outcome. `docs/language/ownership-design.md` §17.9 designs the out-of-room outcome; this issue builds it. It closes the out-of-room item of [[bytes-level-lowering-recursion]].

## The design, in short (§17.9 is the statement)

- The meaning does not learn of room: no new outcome of `Ran`, no parameter of `run`.
- The contract gains one alternative, a resource stop (`Spent`): the code exits with one reserved status at a world whose past is a prefix of a history the meaning reaches at some fuel, or the meaning is stuck at some fuel (`MeetsGoing`'s conclusion). The tracking clause is `Tracked ∨ (¬(room(f, peak) <= i) ∧ Spent)` under the premise `rooms(f) <= i`, a table by routine alone. Today's `Tracks` is its corollary where `room(f, peak) <= i`.
- A call is guarded where its callee can reach the caller (one strongly connected component of the call graph); every other call is not. `rooms(f)` is `f`'s largest frame plus the largest `24 + rooms(g)` over its unguarded calls. A guard tests that `24 + rooms(g)` fits in the room left before the CALL and otherwise jumps to the stop.
- The floor comes from `Stack<M>` and the compiled budget, computed at the entry and kept where the guard reads it.

## Scope, in order

1. **The test before anything is built on it** (§17.9's last paragraph), with the statement written and the theorem's type stated: `down` guarded lowers by evaluation; at a budget its peak fits the first alternative holds; at a budget one frame short the machine's run by evaluation exits with the reserved status after the writes the meaning makes before that depth; a two-routine cycle with different frames; a program with no cycle lowers to today's bytes. Report to the coordinating session before step 2 if the statement has to differ from §17.9.
2. `Spent` and the restated clause in `x86_64_call_contract.hthr`, generic in the world as `Tracks` is; `Site::tracks_meets` re-proved (the stop is a going-clause fact).
3. The guard in the lowering (`bytes_level_routines.hthr`), the constant table and its law; the lowering's theorem re-proved to the restated clause; today's theorem as the corollary by `RoomLaw` at depth. As ruled after step 1 (§17.10):
   - `Program::lower` is the guarded lowering; the probe copy `Program::lower_guarded` (`bytes_level_guard_tests`) is gone when this lands. The acyclic rows' bytes are the witness that nothing else moved (`scripts/linked --check`, `scripts/bytes-level-compare`).
   - The stop is one absorbing alternative: the claims' existing exit (`StopExited`) with a different fact about the exited state, through one bind parameterised by what the exited state satisfies, if it can be one; if not, report why with the two types side by side before building a second.
   - `LowerProgramSpends` discharged (`lower_program_tracks`), `lower_program_tracks_at` its corollary, the readings' hypotheses dropped.
   - The floor established: the whole-program entry (`bytes_level_whole`, `_start`) sets RBP from the stack pointer it is given and the budget, and the process theorem discharges `Entering`'s floor premise from the start state; a probe at the whole-program level; the static refusal where `routine_rooms(entry)` exceeds the budget. An export's prologue: state what it must save (RBP, the host's) and set (the floor); build it only if a linked export row has a cycle (none is expected: FunctionIR's programs call only below).
4. The recursion gate's programs through the new layer by the comparison script: `sum(10)` within its budget, the run-time stop with a small one, the static refusal where `rooms(entry)` exceeds the budget.

## Not here

Dropping a guard under a proved depth bound (a pass, [[bytes-level-passes]]); the heap's stop (the same alternative, with the arena); dying by a signal instead of a status.

## Done when

A routine that calls itself lowers with a guard and a theorem whose premise does not mention the run, the unguarded theorem is its corollary, and a program with no cycle lowers to the same bytes as before.

## Log

- 2026-11-26: Step 1 (statement and §17.9's test by evaluation): Spent, Entered (floor RBP premise), TracksSpent, TracksAt and the corollary tracks_at_of_spent in the contract; call graph, program_guards, routine_rooms (checked by rooms_settled), the guard's code, stop_rooms (lawful, over routine_rooms) and LowerProgramSpends in the routines; guarded emission and an Asm-level machine as probes (bytes_level_guard_tests). Findings: floor in RBP (no data-word load in the model); guard after the argument moves, so every call counts 24 bytes in the table; no-guard-fires is false at depth_rooms (downh), true at stop_rooms. §17.10.
- 2026-11-26: Step 1 verified at 509e585: HEATHER_PR_NATIVE=all scripts/test --pr (no merge base, every file) '== suite: 4140 passed, 0 failed, 3 ignored =='; scripts/linked --check unchanged; scripts/lib-closures clean. Reported to the coordinating session; step 2 waits on its answer.
- 2026-11-26: Step 2 at 20eb5ff: the contract restated (Entering with the floor premise; Tracks = rooms(f) <= i → Tracked ∨ (¬(room(f, peak) <= i) ∧ Spent); Spent = the exited reading at 139 with MeaningPrefix of its world; TracksAt and tracks_at; MeetsDone/Exited with the stop, MeetsGoing with no room by depth via tracked_prefix; RunsAsMeaning with the stop). depth_rooms deleted for stop_rooms. Until step 3 the lowering proves TracksAt (lower_program_tracks_at) and its readings take LowerProgramSpends as hypothesis. HEATHER_PR_NATIVE=all scripts/test --pr: '== suite: 4140 passed, 0 failed, 3 ignored =='; linked --check unchanged.

## Handoff (2026-11-26, after step 2)

**Done.** Step 1 (the statement, §17.9's test by evaluation; findings ruled on, §17.10) and step 2 (the contract restated: `Site::Entering` with the floor, `Site::Tracks` with the spent stop, `Site::Spent` as the exited reading at 139 with `MeaningPrefix`, `Site::TracksAt`/`tracks_at`, the readings, `RunsAsMeaning`; `depth_rooms` deleted for `stop_rooms`). Suite at both: `== suite: 4140 passed, 0 failed, 3 ignored ==`.

**Next, in order (step 3).**
1. Settle with the coordinating session how the stop composes with the claims (condition 1, below); then generalise once at the root.
2. The guarded emission into `Body::emit` (the probe copy in `bytes_level_guard_tests`: `call_prog_guarded`, `File::emit_call_guarded`, the `listed(guards, callee)` case, `Routine::emit_guarded`'s saves ≤ 5 check, `Program::lower_guarded`'s labels from `bound + 1` and `stopped_at`), deleting the probe copy; `rooms_settled` checked in `Program::lower`.
3. Re-prove the region claims with the stop as the escape (done side `Body::emit_emits`/`program_returns`, stop side `Body::emit_stops`/`program_stops`, the call lemmas `call_now_step`/`call_heap_stops` with the guard's code: its block, the `CMP`, the not-taken `JCC`, or the taken one to the stop); `¬(stop_rooms(f, peak) <= i)` from the guard's test by `RoomLaw` at depth.
4. `lower_program_tracks` (discharging `LowerProgramSpends`), `lower_program_tracks_at` its corollary, the readings' hypotheses dropped (`lower_program_meets`, the probes' `*_meets*`, `echo_runs_as`).
5. The floor established (`bytes_level_whole`, `_start` sets RBP from RSP and the budget; the static refusal where `routine_rooms(entry)` exceeds it; a whole-program probe). Export prologue stated, built only if a linked row has a cycle.
6. Witnesses: `scripts/linked --check`, `scripts/bytes-level-compare` (acyclic rows the same bytes; the reach and table computations' cost on scan_token is unmeasured).

**Condition 1, the finding (reported to the coordinating session, no answer yet).** The claims' step lower bound does not let the stop be a plain goal disjunct on the going side:

    Performs(writes, kernel, goal, calls, least)(from) :=
      calls = 0:    ∃ t n, runs(n, from, t) ∧ (least <= n ∧ goal(t))
      calls = k+1:  ∃ t n, runs(n, from, t) ∧ ((least <= n ∧ goal(t)) ∨ kernel.resumes(t, Performs(…, k, least - n)))

    needed, the going stop:  reach `r.io = o` with at least the fuel's count of steps,
                             or reach `Spent`'s exit state with any number of steps.

On the done side and at `StopExited` the bound is zero, so `goal ∨ spent-exit` through the existing `performs_bind` works there. At `StopGoing` the bound is the fuel, and a guard can fire after fewer counted steps (`down` from two, one table frame short: one CALL counted before the guard fires, at fuel three). The kernel trick (`into_callee`'s: the spent exit as a resumption that admits anything) avoids the bound but spends a call with no exchange, which breaks the counts read off the worlds (`linux_performs_exact`, `claims_exact`, `claims_stop_exact`). Proposed: one generalisation at the root, `Performs` with an escape `esc: Running → Type`, its reach disjunct `(least <= n ∧ goal(t)) ∨ esc(t)` (no bound on the escape), today's `Performs` its instance at `esc = False` by a one-line definition, the generic lemmas (`performs_less/up/more/weaken/prefix/after/steps/bind/then_steps`, `Claims`, the claim lemmas) stated once over `esc`. Then the exited stop and the spent stop are both escapes with different facts about the exit state, through one bind.

**Traps.**
- `heather eval` cannot print a value holding `BitVec`s or a large record (it runs out of fuel reading it): read through `halt_code`-style `List<Nat>` encoders.
- A probe whose word is live across a system call must not sit in RDI/RSI/RDX/RAX/RCX/R11 (the moves clobber it): `shout` copies it to R8 first.
- Guarded programs' `Short` label names shift by one (labels from `bound + 1`); acyclic programs' do not.
- `scripts/test --pr` on this branch has no merge base with `origin/master` and runs every file.
- Another session works in `lib/lang/ownership/`: do not edit there.
- 2026-11-26: Handoff after step 2 at 460af9f (suite at 20eb5ff: '== suite: 4140 passed, 0 failed, 3 ignored =='). Condition 1 analysed: the stop is a plain goal disjunct on the done side and at StopExited (bound zero) but not at StopGoing (bound = fuel; a guard fires after fewer counted steps). Proposed one generalisation of Performs with an unbounded escape; reported to the coordinating session. See ## Handoff.
