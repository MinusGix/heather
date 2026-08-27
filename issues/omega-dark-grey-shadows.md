---
title: Extend Omega with certified dark and grey shadows
status: open
labels: [proofs,elaboration,arithmetic,solver]
blocked-by: [omega-linear-arithmetic]
created: 2026-08-27
updated: 2026-08-27
---

Increase Omega's integer completeness beyond the real shadow by implementing
the dark and grey shadow steps of the Omega test. Treat this as a deliberate
solver and certificate extension: a real-shadow survivor remains a structured
stuck result until an additional shadow derives a contradiction.

The Rust search core should continue recording an append-only derivation DAG.
New shadow nodes need independently replayable Heather lemmas, checked integer
rounding, deterministic search ordering, and reachable-node extraction. Use
the pinned Lean Omega checkout for algorithmic comparison while documenting
where Heather's shared certificate architecture differs.

## Acceptance

- Cover systems whose real relaxation is feasible but whose integer problem is
  contradictory, including non-unit coefficient examples.
- Reconstruct every new derivation through ordinary Heather proof terms and
  the kernel gate.
- Preserve structured refusal when all implemented shadows survive.
- Pin search/frontier growth on examples that would otherwise branch badly.

## What it assumes from elsewhere

- **[[omega-linear-arithmetic]]** owns the core constraint representation,
  derivation DAG, and real-shadow implementation.
- **[[omega-performance-telemetry]]** owns reusable growth measurements.
