---
title: Complete kernel reconstruction for CutSat derivations
status: closed
labels: [proofs,elaboration,arithmetic,solver]
area: tactics
milestone: [tac-arith]
blocked-by: [arithmetic-certificate-dag-sharing]
created: 2026-08-27
updated: 2026-10-28
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

## Log

- 2026-10-28: Every CutSat derivation reconstructs (`crates/elab/src/cutsat_cert.rs`): Cooper with a carried divisibility, solve-div, dvd-drop, constant divisibility/diseq/bound conflicts and diseq splits, each through a named `omega.hthr` lemma. Kernel-gated positives and satisfiable mutations are in `lib/_tests/std/tactic/omega_tests.hthr` (Pugh, a generated system per rule). The certificate is one `have` per reachable node, so used-lemma and node reports describe the whole certificate. Closing.
