---
title: Spill only live registers around a verified call
status: closed
labels: [native,x86,ir,proofs]
area: heather-in-heather
milestone: [hih-passes]
created: 2026-10-24
updated: 2026-11-14
---

Each `Call` in the verified lowering spills all eight caller-saved
registers other than RAX (RCX, RDX, RSI, RDI, R8–R11) before the CALL and
reloads all eight after it (`function_ir_lower_calls`, `List::spills` /
`reloads` from `x86_64_stack_runs`), whether or not anything live is in
them. `branches.hthr`'s `keep_twice` (two calls of a leaf) is several
times the old path's size, almost all of it these stores and loads.

What it needs: spill only the registers that hold an id read after the
call (the file knows which id each register holds; `reads` of the
continuation says which are live). The proof side already states the
spill/reload runs over a register list, so the list becomes the live set
rather than the constant one, and `call_restores` asks that every
register the file still claims after the call was in the list: a register
left out is dropped from the file (written `None`), so a later read of it
is a refusal, not a wrong program.

A placement-side refinement after that: prefer callee-untouched choices
for values live across a call, so fewer need spilling at all.

Found measuring [[function-ir-verified-selection-rules]].

## Log

- 2026-11-14: Built. A call's place may be `Spilling(mask)`, a mask over the eight caller-saved registers (`saved_registers`, bit i for the ith; `masked`, `call_saves`), and the call stores and loads those alone. The call's proof takes the list where it had the constant (`call_step`, `call_stages`, `call_returns`, `lend_step` over `saved` with `saved.len() <= 8` and `saves_named(saved)`), and `call_restores` now concludes `file.called(saved, result)`: a caller-saved register the list leaves out is `None` in the file after the call, so a read of an unsaved value is a refusal. With no `Spilling` place a call saves all eight, so earlier placements mean what they did. The planner names the registers whose values the rest of the function reads (`File::plan_call`, from the `Reads` after the call). The placement crosses to Rust as a number (`Place::number`, 32 + mask). Probes: `lib/_tests/native/function_ir/function_ir_spills_tests.hthr` (one register saved and pinned to its instructions with its machine-level theorem, the full mask equal to no place, two refused masks, the planner's choice).

  Counters, cloud box, release, same harness before and after: the linked SHA-256 compression 216,000 to 175,969 instructions a block (19% fewer), the stream 3.56e9 to 2.89e9 a MiB, the scanner 5.11e9 to 3.57e9 over `lib/` (30% fewer). Time moved much less: about 5% on each (11.2 to 12.0 against 9.9 to 11.3 microseconds a block on a noisy box; scanner 36 against 38 MB/s). The stores and loads that went were off the critical path, which the CPU overlaps; the instruction counter is exact and repeatable but is not time, and a pass should state both.

  The refinement named above (prefer callee-kept registers for values live across a call) is [[function-ir-values-in-kept-registers]]'s planner half and is not built here.
