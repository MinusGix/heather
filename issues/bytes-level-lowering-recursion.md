---
title: The bytes level's recursion lowered: the contract's room by call depth, not by fuel
status: open
labels: [native,x86,ownership]
area: heather-in-heather
milestone: [nh-ownership]
created: 2026-11-25
updated: 2026-11-25
---

The bytes level's lowering ([[bytes-level-lowering-routines]]) refuses a routine that calls itself or a routine above it (`File::emit_call`'s `callee + 1 <= bound` with `bound = k`). The meaning ties routines by fuel, so recursion has a meaning; the contract `Site::Entering` fixes the room below a routine's return address (`rooms(f) <= i`) for every fuel, and a recursive routine needs room growing with the depth of calls. Stage 3 needs it back: the native gates include a recursion test (`crates/cli/tests/native_recursion.rs`).

## What exists

- **FunctionIR's levels.** `Function.levels` (`function_ir.hthr`): a function that calls itself is answered `levels` deep. Its meaning is truncated there (`Function::effects_at`, `tied_effects`: a self call below the last level has no effects), so the contract is the levelled one. The room is static: `Function::roomy_levels` checks `level_room(0, frame + 24, levels) <= rooms(k)` and the body under `self_rooms(rooms, k, rooms(k) - level_room(...))`, each level a frame and a call's 24 bytes (`Function::emit_levels_self`).
- **The gate's programs** (`native_recursion.rs`; `lib/_tests/native/runtime/rt_proc_program_tests.hthr`, `runtime_recursion_tests.hthr`): `sum(10)`, non-tail recursive, within 16 levels exits 55; with 9 levels the tenth nested call is refused at run time with the call-depth status 139 (the program compiler's shared too-deep exit); a generated `runtime fn` recursion at the eleven levels it infers, and one short at ten; a stack budget, 64 KiB accepted and 64 bytes refused.

## Constraints (the coordinator's)

- The room is not a function of the fuel: fuel also meters loop passes, so room by fuel would ask a long loop inside a recursive routine for stack it never uses. Room follows call depth, which the fuel only bounds.
- One statement of room: the non-recursive case is its instance, not a second contract.

## Candidates

- **The run answers its peak call depth** beside its outcome (or `peak(p, n, f, args, heap, io)` by `run`'s own recursion, `run` unchanged), and `Site::Entering`'s premise is room for that depth: `room(f, depth) <= i` with `room` a table by routine and depth. For a program whose call graph is acyclic the table is constant past its height, which is today's `routine_rooms`: an instance.
- **A depth the caller passes down**, the callee's contract indexed by it (`Entering` at `(f, d)` asks `room(f, d)`, a call made at `d + 1`), with the done clause only for runs whose peak depth is within `d`. It needs the peak depth of the meaning too, so it is the first candidate with the depth as a parameter.
- Either way the run-time guard of the gate (a nested call past the levels exits 139) is a meaning the language does not have yet: an out-of-stack outcome, or the guard as part of the routine's meaning.

## Done when

`Site::Meets`' room states call depth once, a recursive routine lowers with its theorem, and the recursion gate's programs compile through the new layer.
