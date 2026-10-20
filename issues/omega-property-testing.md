---
title: Differentially property-test Omega search and certificates
status: open
labels: [proofs,testing,arithmetic,solver]
area: tactics
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

## Log

- 2026-08-27: Replaced the original radius-only pure differential check with
  explicitly boxed systems, so exhaustive enumeration is a complete model
  check rather than a heuristic search for small witnesses. The original
  5,400-case grid classifies as 4,414 satisfiable, 986 contradicted, and zero
  real-shadow misses. A second deterministic 20,000-seed rail with four
  generated inequalities classifies as 11,074 satisfiable, 8,835 contradicted,
  and 91 integer-unsatisfiable real-shadow misses. Seed 680 is pinned with its
  directly replayable constraints and minimizes to three inequalities whose
  real region is the singleton `x = -5/2, y = 1`. Pugh's classic nightmare is
  pinned separately. Still open: generate the corresponding Heather source
  subset, minimize frontend failures, and kernel-gate every generated success.
