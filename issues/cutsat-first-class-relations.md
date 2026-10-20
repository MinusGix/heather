---
title: Reflect disequality and divisibility directly into CutSat
status: open
labels: [proofs,elaboration,arithmetic,solver]
area: tactics
milestone: [tac-arith]
created: 2026-08-27
updated: 2026-08-27
---

Make integer disequality and divisibility first-class reflected inputs instead
of obtaining them mainly through logical splitting or internal Cooper state.
Preserve written source evidence and deterministic atom sharing, then pass the
typed constraints directly to CutSat with structured model validation and
kernel reconstruction.

## Acceptance

- Ordinary source propositions for `≠` and divisibility reflect without an
  eager two-way logical split when CutSat supports them directly.
- Candidate models validate every reflected relation.
- Contradictions reconstruct through explicit witness/exclusion lemmas, with
  satisfiable mutations and unsupported forms returning structured state.

## What it assumes from elsewhere

- **[[cutsat-linear-integer-arithmetic]]** owns CutSat constraint semantics.
- **[[cutsat-reconstruction-completeness]]** owns proof replay for the resulting
  derivations.

