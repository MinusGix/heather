---
title: Render Omega stuck states with source-level arithmetic
status: closed
labels: [proofs,elaboration,arithmetic,diagnostics]
blocked-by: [omega-linear-arithmetic]
created: 2026-08-27
updated: 2026-08-27
---

When Omega's real shadow finds no contradiction, render its residual frontier
in the vocabulary of the theorem being checked. Coefficient vectors are useful
for programmatic audits, but diagnostics should show expressions such as
`-17 <= y <= 10` and name the reflected atom order explicitly.

Keep the structured coefficient/bound representation in `OmegaReport`; add
stable atom labels and a source-level rendering rather than replacing machine-
readable data with prose. Ordinary reflection should use the exact shared atom
table used by reconstruction. The low-level explicit `omega::dot` frontend may
use stable indexed fallbacks when its atom row cannot be decomposed safely.

## Acceptance

- A satisfiable affine mutation reports its surviving constraint using the
  original source-level atom name.
- Multi-atom rows render signs, coefficients, zero coefficients, and two-sided
  bounds without exposing derivation IDs or generated proof source.
- `OmegaReport` retains the coefficient vectors and exposes the corresponding
  stable atom labels for tooling.
- Explicit `omega::dot` diagnostics remain deterministic even for a named atom
  row whose elements cannot be recovered from source spelling.

## What it assumes from elsewhere

- **[[omega-linear-arithmetic]]** owns reflection, the real-shadow frontier,
  and success/failure audit channels.

## Log

- 2026-08-27: Closed with source-level residual rendering. Ordinary reflection
  carries its exact shared atom labels into every `OmegaReport`; stuck
  constraints retain coefficients and bounds while also rendering stable
  affine expressions with signs, scaling, zero elision, one- and two-sided
  bounds, and equality intervals. Solver-only auxiliary columns and opaque
  explicit `omega::dot` rows receive deterministic indexed fallbacks. Focused
  rails cover a named two-atom affine interval, the explicit fallback path,
  and renderer edge cases.
