---
title: Expose shared arithmetic reflection for future solvers
status: open
labels: [proofs,elaboration,arithmetic,design]
created: 2026-08-27
updated: 2026-08-27
---

Finish separating canonical arithmetic reflection and certificate plumbing
from Omega-specific interval reconstruction. Future `linarith`, nonlinear
preprocessing, and arithmetic theory propagation should consume the same typed
atoms, source evidence, relations, and checked coefficients without inheriting
integer-specific Cooper search.

This is an extraction from two real consumers—Omega and CutSat—not a generic
solver framework designed in advance.

## Acceptance

- Reflection exposes typed Nat/Int embeddings, canonical affine expressions,
  opaque-atom sharing, source/display spellings, and evidence for supported
  relations through a solver-neutral API.
- Omega and CutSat consume that API without changing existing diagnostics or
  certificates.
- A small second-domain prototype (the initial ordered-ring/`linarith` input
  boundary) demonstrates that no Presburger-specific state leaked into it.
- Unsupported nonlinear terms remain shareable opaque atoms unless a later
  preprocessing pass deliberately interprets them.

## What it assumes from elsewhere

- **[[cutsat-linear-integer-arithmetic]]** supplies the second production
  consumer that makes the extraction concrete.
- **[[grind-port]]** owns whole-solver orchestration, not this representation.

