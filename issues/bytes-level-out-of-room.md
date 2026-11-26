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
- 2026-11-26: Handoff after step 2 at 460af9f (suite at 20eb5ff: '== suite: 4140 passed, 0 failed, 3 ignored =='). Condition 1 analysed: the stop is a plain goal disjunct on the done side and at StopExited (bound zero) but not at StopGoing (bound = fuel; a guard fires after fewer counted steps). Proposed one generalisation of Performs with an unbounded escape; reported to the coordinating session.
- 2026-11-26: Step 3.1 at d0733aa: the root generalised (PerformsOr/ClaimsOr with an absorbing escape; 37 lemmas once over it; the old names instances at False; FunctionIR and certificates untouched). HEATHER_PR_NATIVE=all scripts/test --pr: '== suite: 4140 passed, 0 failed, 3 ignored =='; scripts/linked --check unchanged; scripts/lib-closures clean.
- 2026-11-26: Step 3.2 at ca4885a/1b29c8b: the guarded emission is Program::lower (Body::emit_by with CallGuards; the guard SUB RSP,RBP; CMP RSP,need; JB stop; ADD RSP,RBP at the call's start; lower_plain for acyclic programs; the probe copy deleted). Rulings recorded in ## Handoff: the contract restated with the escape inside the claim; the table goes tight in part 3. scripts/bytes-level-compare: the three rows that differ (copy_window, scan_token, scan_tokens) differ as before (issues/bytes-level-access-view.md), the rest the same.

## Handoff (2026-11-26, second session, after step 3 parts 1–2)

**Done.**
- **Step 3.1, the root generalised** (d0733aa). `Site::PerformsOr` and `ClaimsOr` (and `EntersClaimOr`, `ReturnsClaimOr`) carry an absorbing escape. Every claim lemma is proved once over it (`performs_or_*`, `claims_or_*`, `performs_or_escape`, `reach_or_map`, `reach_goal`). The old names are instances at `False`, with statements unchanged. FunctionIR and the certificates needed nothing.
- **Step 3.2, the guarded emission** (ca4885a, 1b29c8b).
  - `Body::emit_by(g: CallGuards, …)`, with `Body::emit` its instance at none.
  - The guard is at the call's start: `SUB RSP, RBP; CMP RSP, need; JB stop; ADD RSP, RBP`, with `need = 8·count + 8 + rooms(callee)`, ruled by the coordinating session.
  - `Routine::emit_by` refuses six saves.
  - `Program::lower` = `rooms_settled` → acyclic: `lower_plain` (today's bytes); cyclic: `lower_guarded` (labels from `bound + 1`, the stop after the routines).
  - The probe copy is deleted; the guard probes run `Program::lower`.
  - `lower_plain_tracks_at` is the plain lowering's theorem. `lower_program_tracks_at` reads it under the **interim hypothesis** `any_guard(…) = False`.
  - §17.10 has both parts.

**The coordinating session's rulings this round** (to build on, not to reopen):
- **Restate the contract with the escape inside the claim.** `Tracks`: `rooms(f) <= i → n → Answerable → ∃ calls, LinuxPerformsOr(Reached(meaning_n), λ r => ¬(stop_rooms(f, peak_n) <= i) ∧ SpentAt(r), calls, going_least(n, meaning_n), Running(s, io))`.
  - `Tracked` takes the escape as a parameter; today's is its instance at no escape.
  - `SpentAt(r)` = the exit at 139 ∧ `MeaningPrefix(…, r.io.past)`, with no `∃ o` outside.
  - `TracksAt` by closing the escape under the room.
  - `MeetsDone`/`MeetsExited` at their outcome with the escape; `MeetsGoing`'s prefix straight from `SpentAt`.
  - `RunsAsMeaning`: the alternative sits at the trace's end (the outcome's end, or TRet(139) at a meaning-prefix world). No determinism lemma is owed.
  - Amend §17.9's displayed clause in place, pointing to §17.10. Say in §17.10 why the escape is inside: `shout`'s write before the guarded call, and that the conservative table means `¬room` does not decide which end is reached.
- Guard placement and form: as built (above).
- **The table goes tight** (ruled after part 2, superseding §17.10's note that keeps 24 at every call). It should be the tightest table that is lawful for the placement built. With the guard before the call's words, counting them in `need`, a guarded call needs nothing of the caller's table: `rooms(f)` = largest frame + the largest over `f`'s *unguarded* calls of `24 + rooms(g)` (§17.9's original). Put it in when part 3 re-proves the table's law (`rooms_round`/`Body::stop_room`, `rooms_settled`, `stop_rooms_lawful`), not as a separate pass. Let the probes' rooms move (`down`'s 408 and its edges, `shout`'s, `pingpong`'s needs, `downh`'s); they follow the definition. Amend §17.9/§17.10 so the note carries one formula and names the placement it belongs to. If the tight table makes `RoomLaw` or `stop_rooms_lawful` harder, keep the present one and give the reason.

**Next, in order.**
1. The contract restated, as ruled (`x86_64_call_contract`: `Tracked` with the escape, `SpentAt`, `Tracks`, `tracks_at`, the readings and `tracked_prefix` over the escape; `bytes_level_whole`: `linux_runs_as` and `RunsAsMeaning` with the alternative end). Then `LowerProgramSpends` and `lower_spends_tracks_at` follow it.
2. The guard's claim, a stage lemma.
   - From the call node's start, with RBP = `stack.low` (the floored premise) and RSP = `stack.at(d)`: if `need <= d`, arrive after `ADD RSP, RBP` with gprs and memory unchanged; else the escape, reached at the stop's SYSCALL with RDI = 139, RAX = 60 and the world unchanged.
   - The arithmetic: `stack.at(d) − stack.low = d` as a word (`Stack::canonical` gives `low + d < 2^47`); `CMP` with imm32 `need < 2^31`; B ⇔ `d < need`.
   - The guarded call = this then FunctionIR's call claim lifted by `claims_or_weaken` (escape `False` → any).
3. Re-prove the region claims over the escape at `Body::emit_by` (done side `Body::emit_emits`/`program_returns`, stop side `Body::emit_stops`/`program_stops`).
   - The ruling: the existing exit (`StopExited`) becomes an escape with its own facts, through the one bind, not a second path.
   - `¬(stop_rooms(f, peak) <= i)` comes from the guard's `d < need` by `RoomLaw` at depth.
   - The escape is mapped at each call boundary by `performs_or_weaken`'s escape map (the callee's `SpentAt` → the caller's, via `program_grows`).
4. `lower_program_tracks` discharging `LowerProgramSpends`. Drop the interim `acyclic` hypothesis of `lower_program_tracks_at`, and the readings' hypotheses (`lower_program_meets`, the probes' `*_meets*`, `echo_runs_as`).
5. The floor at `_start` (`bytes_level_whole`): RBP from RSP and the budget; the static refusal where `routine_rooms(entry)` exceeds it; a whole-program probe. The export prologue stated, built only if a linked row has a cycle.
6. Witnesses: `scripts/linked --check` and `scripts/bytes-level-compare`, and the cost of the reach and table computations on `scan_token`, as a shape. Then report step 3 whole; the coordinating session merges only then.

**Traps.**
- `heather eval` needs the file to check first: comment out a failing `refl` verdict to evaluate its subject (`halt_code(...)`).
- A `Performs` proof's reach is now `(… ∧ goal) ∨ esc` (at the instance, `∨ False`). A proof that takes one apart reads the goal with `reach_goal`, or matches `Inl(reach) => match reach { Inl(..) .. Inr(never) .. }`; a constructed one is `Inl(⟨…⟩)`.
- `Guards` is FunctionIR's name (`function_ir_lower`): the bytes level's record is `CallGuards`. `bytes_level_lower` cannot import `bytes_level_scope` (it imports lower), hence `among` beside `listed`.
- The probe machine's `low` is the lowest address *stored*. A stop now stores nothing for the call that stops, so the stop verdicts' `low` rose. Statuses and writes are unchanged.
- Run the suite only on a committed tree. Work in a worktree (`git worktree add`) while it runs; `heather check` there reads the worktree's `lib/`.
- Earlier traps still hold: `heather eval` cannot print `BitVec`-holding values; a word live across a system call must not sit in RDI/RSI/RDX/RAX/RCX/R11; on this branch `scripts/test --pr` has no merge base and runs every file; another session works in `lib/lang/ownership/`.
