---
title: Multiply regular Cauchy reals and invert one apart from zero
status: open
labels: [stdlib,mathematics,reals]
created: 2026-10-16
updated: 2026-10-16
---

Define multiplication on `CReal` (`lib/std/creal.hthr`) and the inverse of a
real apart from zero, with their respect proofs and the field laws modulo
`≈`.

Multiplication needs a canonical bound per argument: an integer K above
every term (e.g. `|x_0| + 2`, since every term is within 1 + 1 of `x_0`).
The product reads index 2K(n+1) - 1 of both factors, so the cross terms
stay inside the rate. The inverse of x with `x.Apart(zero)` reads the gap
(k, start) out of the apartness. That gap is data, and the theorems that
build `CReal::Lt` keep their proofs sealed for a client to open
([[theorem-witness-unfolding]]), so the inverse computes.

Acceptance: `mul`, `mul_respects` with a `Respects2` instance, commutativity,
associativity, `mul_one`, distributivity, `ofRat_mul`, and `mul_inv` for an
argument apart from zero, with negative controls at a zero argument.

## What it assumes from elsewhere

- **[[regular-cauchy-reals]]** owns the representation and `≈`. Assumed here:
  the rate is fixed at 1/(n+1) and sums read index 2n+1.
