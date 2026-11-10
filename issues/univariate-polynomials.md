---
title: "Univariate polynomials over a commutative ring: evaluation, degree, division with remainder"
status: open
labels: [stdlib,mathematics,algebra,polynomial]
area: mathematics
milestone: [math-number-theory]
created: 2026-11-10
updated: 2026-11-10
---

Area 4 of the 2026-11-10 ranking. Independent of the gcd round.

`lib/std/tactic/ring.hthr` normalises polynomial expressions and exports
no polynomial type. `hurwitz.hthr` has formal series. Clients waiting:
[[power-series-evaluation]], [[taylor-model-enclosures]],
[[finite-linear-algebra]] (characteristic polynomials later), the
polynomial algebra of `ml-gaussian-states`, CRC and GF(2^n).

## Scope

- `Poly(R)` as coefficient lists up to trailing zeros (a setoid, or
  normalised when `R` decides zero; decide in the round and record why),
  the `CommRing` instance, evaluation as a ring homomorphism, Horner.
- Degree and leading coefficient where `R` decides zero; division with
  remainder by a monic polynomial; the factor theorem; a nonzero
  polynomial over an integral domain has at most `degree` roots.
- Truncation to and from [[formal-power-series]]'s jets.
- `GF(2)[x]` as the instance at `Bool`/`ZMod(2)` with carry-less
  multiplication on words as its computation, for CRC and GHASH.

## Done when

Evaluation is a homomorphism cited by one analysis client, and CRC-32 of
a literal buffer is stated as a polynomial remainder and evaluated.

## What it assumes from elsewhere

- **[[semiring-ring-structure-api]]** owns the ring classes.
