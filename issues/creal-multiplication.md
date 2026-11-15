---
title: Multiply regular Cauchy reals
status: closed
labels: [stdlib,mathematics,reals]
created: 2026-10-16
updated: 2026-10-17
---

Define multiplication on `CReal` (`lib/std/num/creal.hthr`) with its respect
proof and the ring laws modulo `≈`. The inverse of a real apart from zero was
first scoped here and moved to [[creal-inverse]] (2026-10-17).

Multiplication needs a canonical bound per argument: an integer K above
every term (e.g. `|x_0| + 2`, since every term is within 1 + 1 of `x_0`).
The product reads index 2K(n+1) - 1 of both factors, so the cross terms
stay inside the rate.

Acceptance: `mul`, `mul_respects` with a `Respects2` instance, commutativity,
associativity, `mul_one`, distributivity, `ofRat_mul`, with negative
controls.

## What it assumes from elsewhere

- **[[regular-cauchy-reals]]** owns the representation and `≈`. Assumed here:
  the rate is fixed at 1/(n+1) and sums read index 2n+1.

## Log

- 2026-10-17: Landed (docs/library/creal-multiplication-round.md): `CReal::bound` (|x_0| rounded up, plus 2), `mul` reading index (l+1)(2n+2) - 1, and one cross-index estimate `mul_close` behind `mul_respects` (Respects2), `mul_comm`, `mul_assoc`, `mul_add_distr`, `mul_one`, `mul_zero`, `ofRat_mul`; Semigroup and Commutative registered. Even commutativity is not termwise, because the index depends on the bounds in order. The inverse moved to [[creal-inverse]].
