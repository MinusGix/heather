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
3. The guard in the lowering (`bytes_level_routines.hthr`), the constant table and its law; the lowering's theorem re-proved to the restated clause; today's theorem as the corollary by `RoomLaw` at depth.
4. The recursion gate's programs through the new layer by the comparison script: `sum(10)` within its budget, the run-time stop with a small one, the static refusal where `rooms(entry)` exceeds the budget.

## Not here

Dropping a guard under a proved depth bound (a pass, [[bytes-level-passes]]); the heap's stop (the same alternative, with the arena); dying by a signal instead of a status.

## Done when

A routine that calls itself lowers with a guard and a theorem whose premise does not mention the run, the unguarded theorem is its corollary, and a program with no cycle lowers to the same bytes as before.

## Log

- 2026-11-26: Step 1 (statement and §17.9's test by evaluation): Spent, Entered (floor RBP premise), TracksSpent, TracksAt and the corollary tracks_at_of_spent in the contract; call graph, program_guards, routine_rooms (checked by rooms_settled), the guard's code, stop_rooms (lawful, over routine_rooms) and LowerProgramSpends in the routines; guarded emission and an Asm-level machine as probes (bytes_level_guard_tests). Findings: floor in RBP (no data-word load in the model); guard after the argument moves, so every call counts 24 bytes in the table; no-guard-fires is false at depth_rooms (downh), true at stop_rooms. §17.10.
- 2026-11-26: Step 1 verified at 509e585: HEATHER_PR_NATIVE=all scripts/test --pr (no merge base, every file) '== suite: 4140 passed, 0 failed, 3 ignored =='; scripts/linked --check unchanged; scripts/lib-closures clean. Reported to the coordinating session; step 2 waits on its answer.
