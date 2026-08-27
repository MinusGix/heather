---
title: Pin Omega search and certificate growth telemetry
status: open
labels: [proofs,performance,arithmetic,testing]
blocked-by: [omega-linear-arithmetic]
created: 2026-08-27
updated: 2026-08-27
---

Turn Omega's existing audit data into explicit scaling rails. Measure total and
reachable derivations, discarded work, peak constraint-frontier size,
generated certificate source size, and reconstruction/checking time on stable
adversarial families.

The purpose is regression detection rather than a universal benchmark. Counts
that are deterministic should be pinned exactly; wall-clock measurements
should be recorded or bounded coarsely enough to remain reliable. Include
equality chains, dense Fourier--Motzkin projections, balanced hard equalities,
division auxiliaries, and repeated shared opaque atoms.

## Acceptance

- `OmegaReport` exposes every deterministic count needed by the scaling rails,
  including peak frontier size.
- Dedicated tests demonstrate certificate sharing and detect accidental
  exponential reconstruction growth.
- Slow families live in an independently schedulable target with recorded
  timing history.
- Telemetry never changes the trusted certificate boundary.

## What it assumes from elsewhere

- **[[omega-linear-arithmetic]]** owns audit reports and derivation sharing.
- **[[test-suite-target-timing-and-slow-lane]]** owns runner scheduling.
