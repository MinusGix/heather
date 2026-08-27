---
title: Differentially property-test Omega search and certificates
status: open
labels: [proofs,testing,arithmetic,solver]
blocked-by: [omega-linear-arithmetic]
created: 2026-08-27
updated: 2026-08-27
---

Broaden Omega's generated-system testing from the pure real-shadow core to the
complete reflected and reconstructed path. Generate small bounded `Nat` and
`Int` systems, compare them with exhaustive models, and kernel-check every
contradiction certificate Omega claims.

The generator should retain seeds and minimize failures into readable Heather
fixtures. Include equality elimination, GCD rounding, balanced hard equality,
opaque atom sharing, negated relations, and literal division/modulus. Solver
failure is allowed because the implemented shadow set is incomplete; a solver
success in the presence of an exhaustive model is never allowed.

## Acceptance

- Thousands of deterministic small systems are compared against exhaustive
  bounded models in the pure solver.
- A representative generated subset is reflected from Heather source and its
  successful certificates pass the ordinary kernel gate.
- Every failure reports a reproducible seed and a minimized or directly
  replayable case.
- The test target has an explicit resource envelope suitable for CI.

## What it assumes from elsewhere

- **[[omega-linear-arithmetic]]** owns solver and reconstruction correctness.
- **[[test-suite-target-timing-and-slow-lane]]** owns general test scheduling.
