---
title: Compile a loop anywhere in a function, and in a called function
status: open
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
