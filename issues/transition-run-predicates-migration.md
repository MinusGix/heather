---
title: Move the remaining run predicates onto the transition library
status: open
labels: [relation,native,semantics]
area: heather-in-heather
milestone: [hih-passes]
created: 2026-11-09
updated: 2026-11-09
---

[[transition-systems-and-simulations]] made the three native step closures
(`FetchedRuns`, `MachineRuns`, `LinuxStepsN` and their `Star`s) instances
of `lib/std/relation/transition.hthr`. Other run predicates over the same
shape still have their own induction:

- `ExecuteSteps` (`relation.hthr`): a run indexed by an instruction list,
  `StarN` of a step that consumes the list's head.
- `Site::Runs`/`Site::Reaches` (`x86_64_asm_runs`), `Target::Runs`/`RunsK`
  (`native_compile_correct`), `LoopRuns` (`linux_x86_64_wp`,
  `function_ir`): runs with a pre/post or a loop count, many of them a
  `Star` under an invariant (`Star::restrict`) or a `Plus`.
- `SimPaid` (`linux_x86_64_sim_paid`): a tree-to-state simulation where a
  silent tree step costs at least one machine step. On the tree's Tau
  steps it is a `PlusDiagram` into `LinuxStep`; whether stating it so
  shortens `paid_back`/`paid_run_whole` is the question.

## Scope

For each: restate it over `StarN`/`Star`/`Plus` or a diagram where the
shapes agree and that shortens its kit, keeping the old name as a
definition; record why for each one that does not fit.

## What it assumes from elsewhere

- **[[transition-systems-and-simulations]]** owns the kit.
