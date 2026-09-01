---
title: Reconcile FunctionIR branch result placements at machine joins
status: open
labels: [compiler,function-ir,x86,register-allocation,control-flow]
blocked-by: [function-ir-conditional-regions]
created: 2026-09-01
updated: 2026-09-01
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
