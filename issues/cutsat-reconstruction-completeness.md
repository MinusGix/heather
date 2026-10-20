---
title: Complete kernel reconstruction for CutSat derivations
status: open
labels: [proofs,elaboration,arithmetic,solver]
area: tactics
milestone: [tac-arith]
blocked-by: [arithmetic-certificate-dag-sharing]
created: 2026-08-27
updated: 2026-08-27
---

Extend the first simple-Cooper reconstruction slice to every supported CutSat
derivation shape. The search core can already combine bounds and divisibility,
but reconstruction deliberately refuses Cooper cases carrying an existing
divisibility constraint and other deeper symbolic interactions.

## Acceptance

- Every contradiction result produced by the supported CutSat constraint
  language either reconstructs through named Heather lemmas or returns a
  precise unsupported/resource reason naming the derivation node.
- Multiple interacting congruences, nested Cooper trees, constant
  divisibility, and combined bound/congruence conflicts have kernel-gated
  positive tests and nearby satisfiable mutations.
- Used-lemma and reachable-node reports describe the complete outer
  certificate rather than losing work delegated to linear subbranches.

## What it assumes from elsewhere

- **[[arithmetic-certificate-dag-sharing]]** owns economical materialization of
  large reachable proof DAGs.
- **[[cutsat-linear-integer-arithmetic]]** owns supported search semantics.

