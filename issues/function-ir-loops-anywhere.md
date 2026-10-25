---
title: Compile a loop anywhere in a function, and in a called function
status: closed
labels: [native,ir]
area: heather-in-heather
milestone: [hih-passes]
created: 2026-10-25
updated: 2026-10-25
---

[[function-ir-verified-loop-planning]] compiles a recursion on a fuel to a
`Loop` only as the exported function's whole result: its body is a prefix of
values, then `h(w.toNat(), e…)`. Everywhere else the reflector refuses the
call, naming this issue:

- **Under a branch, or followed by more work.** The loop is a register-file
  barrier, so nothing computed before it survives in registers. The
  lowering already allows a loop anywhere (round 5's `emit_calls`); the
  planner's file after it holds the outputs only, so anything read later
  must be in the loop's state. The reflector would carry those words through
  the loop as unchanged state words, the way it already carries the words a
  recursion passes on unchanged.
- **In a function another calls.** The caller's agreement is by `refl`,
  which unfolds the callee's evaluation; a loop's evaluation is not its
  source's recursion by conversion. The caller needs the callee's agreement
  as a rewrite: the same shape as a call of a deciding function
  ([[function-ir-verified-decided-callees]]), which should be solved once
  for both.
- **Two loops in one function**, or a loop's pass containing a loop.

The agreement proof (`function_ir_compile::loop_eval_agrees_from`) is
already stated over any valuation before the loop and any `post`; what is
missing is the certificate meeting the program at a loop that is not the
body's tail (`loop_then_eval` covers `Compose(Loop, post)` only).

## Log

- 2026-10-25: Done. The reflector outlines every fuelled recursion into a FunctionIR function of its own (parameters: the bound, then the state words; body `Compose(Loop(…), post)`), and each call `h(w.toNat(), e…)` anywhere is a `Call` of it: under a branch, followed by more work, in a called function, two in one function, and inside another loop's pass (`examples/x86-native/loop_anywhere.hthr`, run against a C reference in `native_program.rs`). Nothing is carried through a loop as state: the call boundary saves what the caller still needs, as for any call. Outlining costs a call per loop (a CALL/RET and a frame) where the old root-tail loop was inline. The certificate proves the program a function at a time (`function_ir_compile::program_eval_sources` over a `sources` table answering each function by its source; `StructuredRegion::eval_answers` is the congruence that swaps the table), so a caller's proof never unfolds a callee: a function calling another agrees through an expansion that spells each call as `call(k, [..])` (`_expanded`, by `refl` at any `call`) and then `_expands` at the source table. Lowering and layout are stated a function and a stretch at a time (`emit_functions_next`, `names_unique_back`, `jumps_land_back`, `targets_named_back`) so no declaration's fuel bounds the program. Found on the way: [[kernel-fold-probe-evaluates-recursive-arms]] (an exponential in `names_unique`, respelled around).
