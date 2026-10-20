---
title: Extend Omega with certified dark and grey shadows
status: open
labels: [proofs,elaboration,arithmetic,solver]
area: tactics
milestone: [tac-arith]
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

This is now an optional Omega fast-path extension rather than the assumed next
route to complete LIA. [[cutsat-linear-integer-arithmetic]] owns completeness
and integration with future arithmetic consumers. Dark/grey shadows remain
worth implementing if telemetry shows that they close common residuals more
cheaply than invoking CutSat.

## Acceptance

- Cover systems whose real relaxation is feasible but whose integer problem is
  contradictory, including non-unit coefficient examples.
- Reconstruct every new derivation through ordinary Heather proof terms and
  the kernel gate.
- Preserve structured refusal when all implemented shadows survive.
- Pin search/frontier growth on examples that would otherwise branch badly.
- Compare the shadow implementation against a CutSat fallback on the generated
  integrality-gap corpus, not only on hand-picked successes.

## What it assumes from elsewhere

- **[[omega-linear-arithmetic]]** owns the core constraint representation,
  derivation DAG, and real-shadow implementation.
- **[[omega-performance-telemetry]]** owns reusable growth measurements.
- **[[cutsat-linear-integer-arithmetic]]** owns the complete LIA fallback and
  the comparison baseline.

## Log

- 2026-08-27: Complete boxed enumeration exposed 91 real-shadow misses among
  20,000 deterministic generated systems (0.455%). The first miss minimizes to
  three inequalities forcing the non-integral real point `(-5/2, 1)`; Pugh's
  nightmare also survives. This demonstrates a real completeness gap, but the
  observed rate does not justify making full grey-shadow enumeration the
  shared arithmetic architecture. Keep this issue open as a measured Omega
  specialization while pursuing model-based CutSat for completeness.
