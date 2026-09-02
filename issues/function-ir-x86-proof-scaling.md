---
title: Make generated FunctionIR x86 refinement scale past small DAGs
status: open
labels: [compiler,function-ir,x86,proofs,performance]
created: 2026-09-01
updated: 2026-09-02
---

The binary-ALU expansion probed the generated x86 refinement at 20 FunctionIR
nodes and 22 selected instructions. Selection and allocation were effectively
instantaneous, but the end-to-end Heather module had not completed after five
minutes when run alone. The same mixed graph at five nodes and seven
instructions checks in about 64 seconds on the same debug build.

The generator already names machine states and instruction-local result/frame
facts. The remaining suspicious shapes are repeated theorem parameters that
carry the entire `RegionHolds` spine and node equations selected by increasingly
deep `.right` projections. Measure item/frontend/kernel time before changing
the proposition. Likely experiments are named graph-suffix facts, factoring
graph equations out of every placement theorem, and a generated placement-state
certificate whose steps refer to opaque predecessor facts.

## Acceptance

- A mixed 20-node binary-ALU DAG checks comfortably inside the normal test rail.
- A 100-node chain or layered DAG has a bounded stress rail and does not show
  superlinear proof-composition growth.
- Measurements separate selection, source rendering, frontend elaboration,
  and kernel checking.
- The allocator and renderer remain untrusted; stale graph or machine facts
  are still rejected by ordinary elaboration/kernel checking.

## What it assumes from elsewhere

- **[[function-ir-alu-core]]** supplies the mixed-operation workload.
- **[[frontend-large-proof-composition-cost]]** owns general frontend sharing;
  this issue owns generator-side proof factorization that is useful even before
  a general frontend improvement lands.
- **[[x86-block-normal-execution-proof-fuel]]** owns replacing per-instruction
  execution stages with the natural generic functional-to-relational theorem.

## Progress, 2026-09-01

The first scaling cut is implemented and changes the shape rather than raising
fuel. Internal placement theorems now take one compact context record; node
semantics advance through persistent opaque `NodesHold` suffixes; instruction
execution advances through persistent instruction suffixes and opaque stages;
and immutable input-register placements are instantiated directly at their
use state instead of being copied through every intervening instruction.

Measured alone with item timing enabled, debug build:

- the original 20-node/22-instruction module exceeded 300 seconds;
- the staged 5-node module takes 25.3 seconds;
- 20 nodes take 64.5 seconds; and
- 50 nodes take 154.1 seconds.

The 20-to-50 ratio is 2.39× for 2.5× as many nodes. Late node facts remain
flat (roughly 1.5--1.75 seconds each), so the former superlinear projection and
frame-propagation shapes are gone. At 20 nodes, machine framing fell from 80
generated facts/18.4 seconds to 2 facts/0.46 seconds, while value-placement
facts fell from 102/49.9 seconds to 22/30.2 seconds. Execution staging remains
about 1 second per selected instruction and value placement about 1.5 seconds
per node; these linear constants keep this issue open for the 100-node rail.

The ordinary five-node acceptance remains fast enough for the default suite;
the 20-node case is an explicit ignored stress test. Set
`HEATHER_FUNCTION_IR_X86_TIMINGS=1` for item/category attribution and
`HEATHER_FUNCTION_IR_X86_NODES=N` to probe another size.

As an integration-level result, the complete serial `function_ir_x86` test
binary fell from 163.7 seconds before this cut to 106.2 seconds after it, while
adding the larger mixed-operation machinery and retaining stale-model and
alternate-schedule controls.

## Follow-up, 2026-09-02

The full-suite audit after compact-Nat compatibility repairs found one stale
emission assertion: the structured Heather emitter formats a theorem's
proposition on the line after `byte_length():`, while the test still searched
for the legacy one-line spelling. The emitted theorem still states and checks
that the constant/Add block is 13 bytes; the assertion now pins the structured
format, and its focused test passes.

The same full run also shows this target has again outgrown its process rail as
a *collection*: libtest runs two heavy cases inside the binary, and the process
was killed at 152.85 seconds wall by the cumulative 300-CPU-second/4-GiB
envelope before printing a result line. The focused repaired case passes in
22.28 seconds, and all earlier completed FunctionIR targets were green. Do not
hide this by raising the rail: either continue reducing the execution/
placement constants owned here or shard the now-independent test groups as
`issues/integration-test-prefix-reelaboration.md` did for Omega.

The suite is now split into model, checked lowering, source, binary-ALU, and
control-flow test processes, with the explicitly ignored large-DAG probes in a
sixth scaling target. The old `function_ir_x86.rs` is shared fixture code and
deliberately contains no tests of its own. This keeps one canonical
workload/emitter while giving each independent semantic group its own unchanged
process rail; the content-addressed semantic module store prevents the split
from multiplying the expensive checked-library prefix.

The next plain `scripts/test` validates the process boundary under actual
parallel suite load: model 85.4 s, checked lowering 27.1 s, source 79.8 s,
binary ALU 160.5 s, and control flow 213.5 s, all inside their unchanged
individual rails. The former aggregate target now contains no tests and exits
immediately. The run reached 2,289 passes and zero failures; it was formally
incomplete only because the separately owned `omega_div_mod` target was
SIGKILLed near its existing single-workload rail. The accumulated FunctionIR
x86 process failure described above is therefore resolved; the issue remains
open for its original 100-node proof-constant acceptance target.
