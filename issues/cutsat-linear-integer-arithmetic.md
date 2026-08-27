---
title: Build complete certifying LIA with a shared arithmetic substrate and CutSat
status: open
labels: [proofs,elaboration,arithmetic,solver,design]
blocked-by: [omega-linear-arithmetic]
created: 2026-08-27
updated: 2026-08-27
---

Implement the staged design in
`docs/certifying-arithmetic-substrate-design.md`: keep Omega as the fast affine
first pass, extract its reusable reflection/certificate plumbing, and add a
model-based CutSat fallback for complete supported linear integer arithmetic.

The architectural goal is broader than closing Omega's current shadow gap.
CutSat should eventually provide incremental constraints, typed proof
justifications, candidate assignments, resource-limit state, and decision
dependencies that a future `grind` can consume. Future `linarith` and nonlinear
arithmetic share canonical arithmetic reflection and certificate construction,
not the integer-specific Cooper search.

## Acceptance

- Shared affine reflection retains Nat/Int embeddings, opaque-atom sharing,
  deterministic atom labels, checked coefficients, and all current Omega
  behavior.
- The search-only CutSat core classifies the generated 20,000-system rail and
  closes all 91 pinned real-shadow misses, including seed 680's minimized thin
  system and Pugh's nightmare.
- Cooper conflict derivations reconstruct through named Heather lemmas and the
  ordinary kernel gate, with reachable-node sharing and exact used-lemma audit.
- Equality, inequality, disequality, and divisibility constraints are supported
  explicitly; candidate models satisfy every supported reflected constraint.
- Step/resource exhaustion returns a partial model and structured residual
  state, never a satisfiability or contradiction verdict.
- The eventual tactic path tries Omega first and invokes CutSat only after a
  structured real-shadow survivor, with comparative telemetry.

## What it assumes from elsewhere

- **[[omega-linear-arithmetic]]** supplies the landed affine solver,
  reconstruction boundary, and reports from which the shared substrate is
  extracted.
- **[[omega-property-testing]]** owns deterministic generated ground truth and
  kernel-gated frontend generation.
- **[[omega-performance-telemetry]]** owns comparative growth rails.
- **[[grind-port]]** owns whole-solver orchestration and the e-graph interface;
  this issue owns the arithmetic theory module it may eventually call.
- **[[omega-dark-grey-shadows]]** remains an optional measured fast-path
  extension, not a completeness dependency.
