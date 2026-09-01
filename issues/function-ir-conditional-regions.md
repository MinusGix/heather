---
title: Add the first structured Conditional region to FunctionIR
status: closed
labels: [compiler,function-ir,semantics,control-flow,rvsdg]
blocked-by: [function-ir-alu-core]
created: 2026-08-31
updated: 2026-09-01
---

Introduce an intuitively named `Conditional` node owning nested regions after
the straight-line operation and lowering interfaces have real use. This is the
first pressure test of the RVSDG direction: control is structured through
regions and explicit dependencies rather than arbitrary backedges or an
incidental instruction sequence.

The slice must settle how branch inputs, yielded values, multiple results, and
condition typing appear in compact validity and graph denotation. It should
not introduce a general effect system or loops at the same time.

## Acceptance

- Both branches are independently valid nested regions with explicit inputs
  and matching yielded output types.
- Conditional denotation is independent of irrelevant schedules inside each
  pure branch.
- A small conditional function lowers to certified x86 control flow.
- Invalid branch captures, result mismatches, and unavailable dependencies are
  rejected.
- The implementation records which interfaces generalize cleanly toward
  `Loop`, `Function`, and `Apply`, without implementing them speculatively.

## What it assumes from elsewhere

- **[[function-ir-alu-core]]** supplies a useful condition-producing operation
  and an extensible lowering rule boundary.

## Resolution

Implemented with a directly recursive `StructuredRegion` over flat dataflow
leaves, explicit argument and yield interfaces, selected-branch denotation,
host validation and kernel-checked validity examples. The first generated x86
artifact selects between Add and Sub leaves from a materialized one-bit GPR,
executes only that leaf, and proves the common `RAX` result. Invalid captures,
unavailable conditions, invalid leaves, and mismatched yields are pinned as
negative controls.

The follow-up producer composition is also complete: `Sequence` scopes a flat
comparison prefix over the conditional, and a generated certificate carries
the comparison result and protected arguments through the explicit
intermediate machine state before branching.

Leaf encodings are canonical and decoded; physical conditional-transfer bytes
and displacement/layout proofs are intentionally tracked separately in
[[x86-64-conditional-branch-layout]].
