---
title: Reconcile FunctionIR branch result placements at machine joins
status: closed
labels: [compiler,function-ir,x86,register-allocation,control-flow]
area: heather-in-heather
blocked-by: [function-ir-conditional-regions]
created: 2026-09-01
updated: 2026-10-24
---

The first conditional allocator requests the same output register from both
branches. General structured lowering needs an explicit join-placement phase:
independently selected successors may return live values in different
registers, and multiple yielded ports may require parallel edge moves.

## Acceptance

- Compare branch exit placement environments by stable port ID and width.
- Choose a common join environment and synthesize edge moves where required.
- Handle multiple results and cycles in parallel moves without clobbering live
  values.
- Emit local move/frame certificates and compose them with each branch proof.
- Distinguish register pressure, impossible fixed-register constraints, and
  unsupported spill requirements in structured decline errors.

## Log

- 2026-09-20: [[function-ir-recursive-structured-lowering]] now supplies multiple physical
  results with an explicit common destination map used by both branch arms.
  That satisfies fixed-placement joins; independently chosen branch exits,
  parallel edge moves/cycles, spills, and their local certificates remain the
  scope of this issue. [[function-ir-shared-multi-result-dag]] separately tracks
  sharing work across multiple DAG results.
- 2026-10-24: Not planned: what this issue is about was deleted in burn B2 (docs/native/native-program-logic-design.md §3.2). The verified `compile-x86` path (`function_ir_compile`, `compiled_returns`) replaces it; the last commit with the old code is `82521ea`.
