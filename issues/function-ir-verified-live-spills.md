---
title: Spill only live registers around a verified call
status: open
labels: [native,x86,ir,proofs]
area: heather-in-heather
milestone: [hih-passes]
created: 2026-10-24
updated: 2026-10-24
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
