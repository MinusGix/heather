---
title: Make generated FunctionIR x86 refinement scale past small DAGs
status: open
labels: [compiler,function-ir,x86,proofs,performance]
created: 2026-09-01
updated: 2026-09-01
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
