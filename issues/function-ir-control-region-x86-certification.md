---
title: Certify block-argument ControlRegion lowering through the physical x86 join
status: closed
labels: [compiler,function-ir,x86,control-flow,proof]
created: 2026-09-02
updated: 2026-09-03
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

## Result

Completed 2026-09-03. `generate_control_region` now emits one checked physical
artifact for the `max_plus` diamond: canonical prefix/TEST/JZ/true-transfer/JMP/
false-transfer bytes, exact rel8 targets and common join RIP, canonical shared
continuation decoding, linked execution, selected SSA bindings, and final RAX
refinement from `ControlRegionHolds`.

The proof crossed default kernel fuel when x86 execution, dependent join
evidence, and arithmetic were composed in one declaration. The landed shape
separates machine computation from semantic selection, uses a generic
`control_join_cases` eliminator, exposes block-argument heads/tails one
constructor at a time, and composes named endpoints. No fuel or kernel change
was needed. A focused forged edge claims `MovRR(R9, Rsi) = MovRR(R8, Rsi)`
and is rejected by the kernel; ordinary stale execution/artifact controls
remain elsewhere in the x86 suite.

On a quiet debug run the honest generated module checked in 94.9s (50.7s
kernel, 44.2s frontend). The dominant declarations remain linked branch
decode/layout/RIP facts rather than final FunctionIR refinement. Linked
execution and branch-span support were split into bounded semantic modules;
an attempted aggregate decode-evidence record was removed because its derived
projection image exceeded the syntax-node rail while duplicating facts the
certificate already exposes separately.
