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
- 2026-11-26: Step 3.2 verified at f89545b: HEATHER_PR_NATIVE=all scripts/test --pr '== suite: 4140 passed, 0 failed, 3 ignored =='; scripts/linked --check unchanged; scripts/lib-closures clean. Handoff (second session) below.
- 2026-11-26: Step 3 item 1 at 057f2f0: the contract restated with the escape inside the claim (Tracked with the escape, SpentAt, OutOfRoom, TracksAt closing it, MeetsDone/MeetsExited at their outcome, tracked_prefix and performs_or_meet over an exiting escape; bytes_level_whole's LinuxRuns and RunsAsMeaning with the alternative at each branch's end). HEATHER_PR_NATIVE=all scripts/test --pr: '== suite: 4140 passed, 0 failed, 3 ignored =='; scripts/linked --check unchanged; scripts/fmt --check, scripts/lib-closures clean.
- 2026-11-26: Step 3 item 2 at 4a04831: the guard's stage lemma Site::guard_claims (bytes_level_lower), with Stack::offset_small, Stack::room_word, guard_immediate, guard_taken. Item 3 foundations at 44ea99a: Kernel::escaping and its conversions (x86_64_stack_runs), HistoryExtends of the meaning (bytes_level_scope, bytes_level_routines). The coordinating session accepted item 1 as built (RunsAsMeaning as LinuxRuns) and the kernel-step encoding with conditions (below).

- 2026-11-26: Verified at 37021c5 (items 1–2 and item 3's foundations): HEATHER_PR_NATIVE=all scripts/test --pr '== suite: 4140 passed, 0 failed, 3 ignored =='. The ceiling count at K_E (Site::escaping_ceiling) after it, checked by heather check on the contract and its importers. Handoff (third session) below.
## Handoff (2026-11-26, third session, after step 3 items 1–2 and item 3's foundations)

**Done.**
- **Item 1, the contract restated** (057f2f0; suite `== suite: 4140 passed, 0 failed, 3 ignored ==`). Accepted as built by the coordinating session. `Tracked(…, outcome, esc)`, `SpentAt`, `OutOfRoom`, `Tracks` in `LinuxPerformsOr(goal, OutOfRoom)`, `TracksAt` at no escape. `RunsAsMeaning` is `LinuxRuns` (the trace read off each branch's world), with `RunsAs` of one trace as its corollary where the ends pin one world (`linux_runs_as`, `tracked_runs_as`). §17.10 "Step 3, part 3".
- **Item 2, the guard's stage lemma** (4a04831). `Site::guard_claims` (bytes_level_lower) is a `ClaimsOr` at no call and bound zero. From the call node's start, RSP at `stack.at(d)` and RBP `stack.low`: if `need <= d`, it arrives after the ADD with every register as it was; else it escapes at the stop's SYSCALL (`Site::StopAt`). The arithmetic: `Stack::offset_small`, `Stack::room_word`, `guard_immediate`, `guard_taken`.
- **Item 3's foundations** (44ea99a).
  - `Kernel::escaping(kernel, E)`: E's states are calls with nothing owed.
  - `performs_or_of_escaping` converts a claim at `escaping(E)` into the root's `PerformsOr(goal, E)`, at the same count; `escaping_of_performs_or` and `claims_escaping` go the other way at one call more; `performs_or_kernel` widens a kernel.
  - `HistoryExtends`, of the meaning alone: `Body::run_extends`, `Routine::call_extends`, `program_extends`.
  - The ceiling count at `K_E` (x86_64_call_contract): `Site::linux_escaping`, `Site::escaping_reaches`, `Site::escaping_ceiling` (a claim whose goal's and escape's worlds are no longer than `top`'s has the count `|top| − |from| + 1`), `ceiling_absurd`, `extends_len`.

**The coordinating session's conditions on item 3** (ruled; build on them):
1. The contract's statement does not change: `Tracks` stays in `LinuxPerformsOr(goal, E)`. `K_E = linux_kernel(stack).escaping(E)` is the regions' working form. There is **one** conversion at the routine boundary (`performs_or_of_escaping`), and nothing above the boundary mentions `K_E`.
2. Counts in the regions may change. Say in §17.10 what read exact counts before (`claims_exact`, `emits_now_exact`, `claims_stop_exact`, `linux_performs_exact`) and where each reading now gets what it needs. Exactness, if still needed, is had at the no-escape instance, not by a second mechanism.
3. One absorbing alternative. Say which encoding carries the meaning's own exit (`StopExited`). If `K_E` can carry the spent stop and the meaning's exit as escapes with different facts, do so and retire the separate path; otherwise say in one sentence in §17.10 why the meaning's exit stays a goal. Not three ways for a region to end in an exit.
4. `HistoryExtends` stays of the meaning alone (done).
5. Write a short paragraph in §17.10 on why two forms exist: the escape is *stated* with `esc` at the contract and *carried* as a kernel step through the regions, with one conversion between them.
6. The tight table stays. A guarded call's `24 <= d` (FunctionIR's `call_step_claim` asks it at every call): prove "a guarded callee calls, so its table entry holds its largest frame, so `need >= 24`" from `program_guards` and `routine_rooms` if that needs no real graph reasoning. Otherwise an emission check `24 <= need` is acceptable, but then §17.10 must say it is a test standing in for an invariant, and a probe must show it never refuses the guard tests' programs.
7. Do not restructure `Loop` (issues/bytes-level-loop-exits.md comes after this work).

**The plan for item 3 (designed, not built).**
- **Counts.** An escape at `K_E` spends one call. So a region's count cannot be `calls_between(before, after)`: a guard firing at a call whose callee makes no exchange has no call to spend. Existential counts do not compose either. FunctionIR's `may_emit_claim_seq` wants one count for every `mid`, which is why today's `emits_now_up` lifts each part to the whole's count.
- **Ceiling counts.** Fix, for a whole routine's proof, a ceiling world `TOP`: the outcome's world, `a.io` done or the stop's world. Give every region from `before` the count `|TOP.past| − |before.io.past| + 1`.
  - Every branch makes at most that many kernel steps. A goal branch makes its world's exchanges, at most `TOP`'s. An escape branch makes its world's exchanges and one more, and its world is at most `TOP`'s.
  - The one new exactness lemma is the ceiling recount at `K_E` (built: `Site::escaping_ceiling`, with `escaping_reaches`), the analogue of `linux_performs_exact`.
  - Seq is then today's proof: lift the rest's ceiling count to the first's by `Between`, bind, recount. So is the branch's (both arms at the same ceiling).
- **The escape `E`** for routine `f` entered at `i` on `(args, heap, io)` at fuel `n`, cap `p`: `E(r) = exit 139 at r ∧ ¬(stop_rooms(f, p) <= i) ∧ Extends(TOP.past, r.io.past)`.
  - At the top, `Extends(TOP, w)` gives `MeaningPrefix` at fuel `n` (TOP is the outcome's history).
  - `¬room` at a firing guard: by `RoomLaw(stop_rooms)` at `p`, `cap >= 1` (a call is in the facts), and `stop_rooms_over` (`routine_rooms(h) <= stop_rooms(h, p−1)`). So `room(f, p) <= i` gives `need <= d`.
  - A callee's E maps to the caller's by RoomLaw at `p` (the callee's `p−1`) and `Extends(TOP, a.io)`.
- **The world fact at a guard.** Each region's `facts` gain `Extends(TOP.past, after.io.past)`. `may_emit_now_seq` derives the first part's from the rest's `Holds(mid, after)` by a Holds-level `Body::holds_extends`, from `HistoryExtends` of the answers. Put it in bytes_level_scope or routines: lower cannot import scope. At the call region, `Extends(TOP, before)` is facts plus the callee answer's extension.
- **The region family.** Generalise in place, not beside: `EmitsNow` and `StopsHeap` take `(E, TOP)` and the ceiling count over `Body::emit_by(g)`. The old family is the instance at `E = False`, and there `K_E` is the Linux kernel up to `performs_or_kernel` both ways. Leaves, `Sys` and `Exit` lift by `performs_or_kernel`.
  - The guarded call is `guard_claims`, then `claims_escaping` (the guard's escape into `K_E`, at one call), then FunctionIR's call claim at `K_E`.
  - `CalleesReturn` becomes the callee's claim at `K_{E_g}` under `routine_rooms(g) <= i` (not depth), widened to the caller's by `performs_or_kernel`.
- **The routine induction** (`program_returns`, `program_stops`, `program_tracks`) restated at the routine table: an unguarded callee is entered with `routine_rooms(g) <= i` from the tight table (`rooms_settled`), a guarded one from the guard's `need <= d`. Then `lower_program_tracks` at the boundary by `performs_or_of_escaping`, `lower_program_tracks_at` its corollary by `tracks_at`, and the `acyclic` hypothesis and `LowerProgramSpends` hypotheses dropped.
- **The meaning's exit** (condition 3): look first at whether `StopExited` can be an escape of `K_E` with its own facts (an exit at the status in the stop's world). The stop side's `least` is zero there, so it may fold in.

**Next, in order.** Item 3 as planned above, with the tight table. Then item 4 (`lower_program_tracks`, the interim hypotheses dropped). Item 5: the floor at `_start`, the static refusal, a whole-program probe; the export prologue stated. Item 6: the witnesses and the cost shapes. Then step 4. Report when step 3 is whole.

**Traps.**
- Never edit the main tree while a suite runs. This session did once, briefly, and moved the edit out. Use `git worktree add` with its own `HEATHER_CACHE_DIR`. Run `scripts/fmt` and `scripts/lib-closures` in the main tree: in a fresh worktree they build a binary from scratch.
- `import memory;` in bytes_level_lower clashes (`Agrees`): use `BitVec::toNat_add_mod` and `Nat::mod_of_lt` (`rip_toNat`).
- `scripts/issue log` appends at the file's end, after this section: move the line into the Log.
- Earlier traps still hold: `heather eval` needs the file to check first and cannot print `BitVec`-holding values; `Guards` is FunctionIR's, the bytes level's record is `CallGuards`; a reach is `(… ∧ goal) ∨ esc` (`reach_goal` at no escape); the probe machine's `low` is the lowest address stored; run the suite only on a committed tree; on this branch `scripts/test --pr` has no merge base and runs every file; another session works in `lib/lang/ownership/`.
