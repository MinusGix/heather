---
title: Compile calls to procedures with frames, derived contracts and a register convention
status: open
labels: [native,x86,compiler]
area: heather-in-heather
milestone: [nh-procedures]
created: 2026-10-31
updated: 2026-11-01
---

Round R8 of `docs/compiler-milestones-proposal.md` (§4.2 N2, §7), milestone `nh-procedures`: calls that are
not inlined.

## Scope

- A compiled call to a procedure, with its frame on the process stack ([[io-image-process-stack]]), its contract derived from its body ([[native-procedure-contracts]]), and a register convention ([[native-register-moves-and-convention]]).
- Recursion that is not a tail loop.
- `grep -F`, with a shared line-buffer helper, as the customer (it moved here from `hih-tools`).

## Done when

A helper called from several sites is emitted once, a non-tail recursive function compiles, and `grep -F` passes GNU tests under `LC_ALL=C`.

## Log

- 2026-10-31: Design: docs/native-procedures-design.md (a procedure table beside main, Perform(procedure, args, results); words by value and the callee's own, buffers shared; calls nest at most Source.depth deep, one deeper exits 139; compiled as callee-saves-its-locals into a frame on the process stack, homes global; the proof carries frames as a ghost list read through Target::argv). Slice 1 landed: the source (Procedure, Perform, Source.procedures/depth, Stmt::denote over a Performs() handler, Source::performs by depth, grows for both, a call's liveness), the compile refusing Perform (refusal reason 14), probes in lib/_tests/native/native_source_tests.hthr (a non-tail recursion, the depth exit, a callee's locals given back, a shared buffer, one helper from two sites).
- 2026-11-01: Design revised before slice 2's proof (docs/native-procedures-design.md §2, §3): a callee starts with every word zero but its parameters and gives back only its results and buffers, and the caller saves the words it needs after the call (pushed before the CALL, popped after). Callee-saves cannot be proved: the callee's claim speaks only of the words live at its end, not of homes it never names. The compile refuses a procedure whose body reads a word other than a parameter. Slice 1's probes updated (a callee starts from zero).
