---
title: Compile every structured region as a leaf of the effectful source
status: open
labels: [native,x86,proofs]
area: heather-in-heather
milestone: [hih-pl-source]
created: 2026-10-25
updated: 2026-10-25
---

`Stmt::emit` (`lib/native/native_compile.hthr`) compiles a `Compute` leaf
only when it is a `Dataflow` region whose inputs and outputs fit the
registers S4's `Region::lower` places them in (`Prog::leaf`, `leaf_checks`).
`Sequence`, `Compose`, `Conditional`, `Call` and `Loop` regions are refused,
and so is a dataflow region with more live values than registers. Found
while proving S3.2 ([[native-effect-source-compiler]], 2026-10-25).

## Scope

- Each structured region form compiled by S4's lowering of it, entering
  `Target::goes_leaf`'s place in `Stmt::emit_runs` with that lowering's
  theorem (`function_ir_lower`'s structured forms, the bounded loop of
  [[function-ir-lowering-loops]]).
- Leaves that spill: their contract changes memory below RSP, so the
  invariant `Target::Placed` must survive a frame. That is the footprint of
  [[wp-proved-memory-contracts]], or a frame range added to the region's
  layout.
- `Call` regions: a total function lowered by S4 and called from the leaf
  ([[wp-callee-from-lowered-function]] gives the callee side).

## What it assumes from elsewhere

- **[[function-ir-verified-lowering]]** owns the lowerings and their
  theorems; this issue only plugs them into the statement induction.
