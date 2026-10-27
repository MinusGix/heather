---
title: Compile every structured region as a leaf of the effectful source
status: open
labels: [native,x86,proofs]
area: heather-in-heather
milestone: [hih-pl-source, hih-tools]
created: 2026-10-25
updated: 2026-10-27
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

## Log

- 2026-10-26: Re-scoped by `docs/native-real-programs-plan.md` (§3.4, round 4): compile every region form memory-resident, as S3.2 compiles statements (each node loads its operands from slots, computes, stores), with no register-pool limit; S4's `Region::lower` stays as the better lowering where a dataflow leaf fits. `Call` regions stay refused (the builder, [[native-source-builder]], inlines). Done when `tr`'s byte map lowers as a bounded FunctionIR loop and a 40-node leaf compiles. Probe: a 15-node leaf is refused today with no reason given.
- 2026-10-26: [[native-source-bytes]] compiles a leaf that is all pure or exactly one byte node (`Prog::computes`); a leaf mixing pure nodes with `BufferLoad`/`BufferStore` is refused. Splitting such a leaf at each byte node, as the plan's §3.1 describes, belongs to this round's memory-resident compile.
- 2026-10-27: [[native-source-builder]] landed. The builder cuts nodes into leaves with `List::fits_leaf` (lib/native/native_build.hthr), a copy of what `Prog::computes` takes today; when mixed or memory-resident leaves land, relax that predicate (and update the lowerings fixed in lib/_tests/native/native_build_tests.hthr).
