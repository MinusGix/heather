---
title: Build positive naturals and unreduced rational numbers
status: open
labels: [stdlib,mathematics,arithmetic,setoids]
created: 2026-09-02
updated: 2026-09-02
---

Define a structurally positive denominator type and unreduced rational
representatives with integer numerators. Mathematical equality is
cross-multiplication equivalence; representation identity remains available.
This avoids making normalization, gcd, or non-structural termination a
prerequisite for rational arithmetic.

Implement embedding, signs/order, addition, multiplication, inverse under an
apartness/nonzero hypothesis, and respectfulness. Prove the equivalence laws
and ordered-field-facing facts needed by later real probes. Normalized
fractions may be a later representation connected by an isomorphism.

## What it assumes from elsewhere

- **[[setoid-core-api]]** owns explicit equality modulo representation.
- **[[cancellative-algebra-api]]** owns the cancellation lemmas needed by
  cross-multiplication.

## Log

- 2026-09-02: Filed as both useful arithmetic breadth and the first serious
  setoid customer.
