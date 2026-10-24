---
title: Meet a Wp callee contract from a lowered function's theorem
status: open
labels: [native,x86,proofs]
area: heather-in-heather
milestone: [hih-pl-wp]
created: 2026-10-24
updated: 2026-10-24
---

`Wp`'s `CallTo` enters a function by its `Callee` contract
(`lib/std/os/linux/linux_x86_64_wp.hthr`), and `Callee::Returns` is met
either by `Wp` over the function's body (`Callee::returns_by`) or by steps to
its return (`Callee::returns_of_steps`). S4's verified lowering proves a
lowered function as `Site::Returns` (`lib/std/arch/x86_64/x86_64_stack_runs.hthr`):
machine steps over a `Stack<M>`, the program resident at the site, a
postcondition over the states. Nothing yet turns the second into the first,
so a compiled function cannot be the callee of a `Wp` program.

## Scope

- A view that holds of a stack region (`DataRegion::stack`) and the
  program's code gives what `Site::Returns` asks: `Site::Resident`, RSP at
  `stack.at(i)` with the return address read there.
- The bridge: from `Site::Returns(stack, entry, pre, post)`, a `Callee` whose
  pre/post are those read through the view, with `Callee::Returns` proved by
  `returns_of_steps` (`linux_steps_of_machine` turns the machine steps into
  Linux's). The view after the call is read off the memory the callee
  returns with; for the buffer view that is the region's cells.
- One control: a FunctionIR function, lowered and proved by S4, called from a
  `Wp` program.

## What it assumes from elsewhere

- **[[wp-stack-items]]** owns `Callee` and the `CallTo` arm.
- **[[function-ir-verified-lowering]]** owns `Site::Returns` and the lowering's
  theorem.
- **[[io-image-process-stack]]** owns the process's stack region; until it
  lands, a control may use the frame as its stack, as `linux_wp_call` does.
