---
title: Probe regular Cauchy reals constructively
status: open
labels: [stdlib,mathematics,reals,analysis,setoids]
created: 2026-09-02
updated: 2026-10-16
---

Implement a small executable presentation of regular Cauchy reals over
rationals, with explicit approximation rate or modulus and extensional setoid
equality. Probe rational embedding, arithmetic, apartness/order, and one
diagonal completeness construction.

The output is a representation/design probe, not a full analysis library.
Measure proof ergonomics and computation, and list every use of choice,
extensionality, proof irrelevance, or classical reasoning (ideally none in the
core).

## What it assumes from elsewhere

- **[[positive-naturals-and-rationals]]** owns rational arithmetic.
- **[[real-completeness-interfaces]]** owns the abstract capability names.

## Log

- 2026-09-02: Split from [[real-number-foundation]] for a concrete
  computational presentation.
- 2026-10-16: First round (docs/regular-cauchy-reals-round.md): `lib/std/creal.hthr` has the representation (sequences at the fixed rate 1/(n+1)), `≈` as eventual closeness with the start index as data, the `Rat` embedding (respects, reflects, additive, strictly monotone), negation and addition with the additive laws, and `<` as an eventual gap with cotransitivity, apartness and tightness. No assumption enters the core. Data-carrying proofs are `fn`s, so moduli and gaps evaluate. Remaining here: the diagonal completeness construction. Split out: [[creal-multiplication]], [[creal-order-and-bishop-bridge]].
