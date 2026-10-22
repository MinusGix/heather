---
title: Finite linear algebra over a ring
status: open
labels: [stdlib,mathematics]
area: mathematics
milestone: [ml-layers]
created: 2026-10-21
updated: 2026-10-22
---

Vectors `Fin n → R` and matrices over a commutative (semi)ring: sums,
scaling, dot product, matrix-vector and matrix-matrix products, transpose,
identity, quadratic forms, Gram matrices, and positive (semi)definiteness
over an ordered field with a certificate that can be checked by evaluation
(an `LDLᵀ` factorisation at `Rat`). ML is the first customer
(`docs/wick-survey.md` §4.1): layers, NTK Gram matrices, conditioning
constants, and the symmetry results (bracket saturation is a matrix
commutator computation).

Spectral theory (eigenvalues, the finite spectral theorem) is a later step
and needs a constructive treatment over `CReal`; do not assume it here.

## What it assumes from elsewhere

- **[[big-operator-semantics]]** owns the notation for sums. Assumed here:
  finite sums over `Fin n` with reindexing and exchange of order.

## Log
