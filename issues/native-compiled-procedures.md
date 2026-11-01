---
title: Compile calls to procedures with frames, derived contracts and a register convention
status: closed
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

- 2026-10-31: A builder tool can call a reflected word function now (`call`, `program`; [[native-build-reflected-helpers]]): such a tool is refused by write-elf until calls compile here, and is a ready customer (lib/_tests/native/native_build_tests.hthr's `raised_status`).
- 2026-10-31: Design: docs/native-procedures-design.md (a procedure table beside main, Perform(procedure, args, results); words by value and the callee's own, buffers shared; calls nest at most Source.depth deep, one deeper exits 139; compiled as callee-saves-its-locals into a frame on the process stack, homes global; the proof carries frames as a ghost list read through Target::argv). Slice 1 landed: the source (Procedure, Perform, Source.procedures/depth, Stmt::denote over a Performs() handler, Source::performs by depth, grows for both, a call's liveness), the compile refusing Perform (refusal reason 14), probes in lib/_tests/native/native_source_tests.hthr (a non-tail recursion, the depth exit, a callee's locals given back, a shared buffer, one helper from two sites).
- 2026-11-01: Design revised before slice 2's proof (docs/native-procedures-design.md §2, §3): a callee starts with every word zero but its parameters and gives back only its results and buffers, and the caller saves the words it needs after the call (pushed before the CALL, popped after). Callee-saves cannot be proved: the callee's claim speaks only of the words live at its end, not of homes it never names. The compile refuses a procedure whose body reads a word other than a parameter. Slice 1's probes updated (a callee starts from zero).
- 2026-11-01: Slice 2 landed: calls compile (each procedure once, at label `Succ(index)`, after `main` and exit 0; the shared depth exit last) and the compile is proved once. `lib/native/native_compile_perform.hthr` gives the call site's code as claims of trees (the frame entered and the room counted down, the saved words pushed, the arguments into RDI…R9, CALL, the callee's way in and out, the words popped, the frame left, the results taken); `Target::Hosts` and `Source::calls_at` (native_compile_correct) prove every call at every depth by induction on the depth, the callee's body by its own `Stmt::emit_runs` at the callee's activation. `native_compile_correct` now covers every source, so `elf_simulates`, `elf_file_simulates`, cat and write-elf drop the bare premise. `Source::refusal` names a call that does not fit (14) and a procedure that does not compile (15). The non-tail recursive sum called from two sites compiles with its body emitted once (lib/_tests/native/native_compile_tests.hthr). Next: slice 3 (write-elf for procedures, the builder's proc form, an ELF test that runs the recursion), then grep -F.
- 2026-11-01: Slice 3 landed: write-elf compiles sources with procedures and the builder has `proc`, `perform` and `depth` (lib/native/native_build.hthr). `Source::spelled` spells `Perform` and procedures; write-elf reads the procedures' code and the shared exit after `main` and proves the compile by `Source::compile_calls_of`. `procedures_run` (crates/cli/tests/native_cat.rs) runs the non-tail recursive sum called from two sites (exit 9), a call past the depth (exit 139), and a builder tool summing 0..n for the n bytes read (`summed_input`, lib/_tests/native/native_build_tests.hthr). A tool with procedures is lowered whole (no part-at-a-time lowering yet), and the Rust allocator mirror leaves sources with procedures to the fork. Next: slice 4, grep -F; the allocators' loop sets must cover procedure bodies first.
- 2026-11-01: 2026-11-01: Slice 4 landed, and the issue is done. `grep -F PATTERN` (`grep_f_tool`, lib/native/native_tools.hthr) is a builder tool whose line test and write is one procedure, `finish`, called from two sites (a newline, and the input ending inside a line) and emitted once; `compiled_grep_f_runs_as_gnu_grep` (crates/cli/tests/native_tools.rs) runs it beside GNU's `grep -F` under `LC_ALL=C` over random inputs and patterns, lines written and exit status equal. The allocators pass and colour procedure bodies (`List::bodies_needs`, `bodies_graph`, `bodies_weights`; `Homes::or_else` falls back when a body fails the check), and write-elf states each procedure's body a part at a time (`Procedure::code_of`, `List::procedures_code_of`), since grep's body overran one `refl`. Residue: [[native-procedures-write-elf-capacity]] (part-wise lowering and the Rust allocator mirror for procedures); the contract and the register convention stay with [[native-procedure-contracts]] and [[native-register-moves-and-convention]].
