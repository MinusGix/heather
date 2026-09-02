---
title: Certify block-argument ControlRegion lowering through the physical x86 join
status: open
labels: [compiler,function-ir,x86,control-flow,proof]
created: 2026-09-02
updated: 2026-09-02
---

`ControlRegion` now validates and executes a real SSA diamond and the x86
selector produces its prefix, selected edge-transfer blocks, common register
interface, and one shared continuation.  The remaining boundary is a complete
checked artifact rather than only a checked lowering plan.

## Acceptance

- Render both selected edge-transfer blocks as canonical instruction blocks.
- Link prefix, `TEST`/`JZ`, true transfer, `JMP`, and false transfer with the
  existing `LinkedConditionalBlock` layout/decode/execution theorems.
- Start the continuation at `linked_join_start` and prove its canonical block
  executes once after either predecessor.
- Turn selected `BlockArgumentsHold` equalities plus edge register effects into
  `ValuePlaced` facts for every join parameter.
- Prove the final `RAX` result refines `ControlRegionHolds` for `max_plus`.
- Expose one byte stream and one execution artifact for the complete graph.
- Add a dishonest edge binding or destination placement control that the
  kernel rejects.

## Follow-up

The first parallel-copy planner declines cycles.  Once a graph naturally
produces a cyclic register permutation, add a scratch-register or stack-based
cycle breaker and certify that local transfer independently.
