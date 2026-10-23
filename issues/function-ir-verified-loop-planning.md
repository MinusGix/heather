---
title: Reflect and plan bounded loops for the verified compile path
status: open
labels: [native,ir]
area: heather-in-heather
milestone: [hih-passes]
created: 2026-10-23
updated: 2026-10-23
---

[[function-ir-verified-lowering]] round 5 lowers and proves FunctionIR's
bounded `Loop`, with placements written by hand. Round 4's `compile-x86`
path has no route to it: the reflector
(`crates/elab/src/function_ir_source/program.rs`) refuses recursion, and
`StructuredRegion::plan_from`'s `Loop` arm places nothing. Two pieces are
missing:

- **The reflector.** Structural recursion, or a `fuel`/measure-bounded
  helper, becomes a `Loop` with `bound` taken from the measure
  (`loop_runs_unexhausted`'s reading: the measure at entry plus one in
  general). The certificate's `refl` agreement then needs the evaluator's
  loop to unfold against the source's recursion, which is untested at open
  arguments.
- **The planner.** It must pick the state, counter and flag registers,
  pairwise apart and caller-saved, as `LoopRegisters::Apart` requires.
  The loop is a barrier, so the planner's file after it is the outputs and
  the exhausted bit only.

The old per-function loop path (`function_ir_loop`) is what B2 replaces
with this.
