---
title: Probe regular Cauchy reals constructively
status: open
labels: [stdlib,mathematics,reals,analysis,setoids]
area: mathematics
milestone: [math-reals]
created: 2026-09-02
updated: 2026-10-17
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
- 2026-10-16: First round (docs/regular-cauchy-reals-round.md): `lib/std/num/creal.hthr` has the representation (sequences at the fixed rate 1/(n+1)), `≈` as eventual closeness with the start index as data, the `Rat` embedding (respects, reflects, additive, strictly monotone), negation and addition with the additive laws, and `<` as an eventual gap with cotransitivity, apartness and tightness. No assumption enters the core. Data-carrying proofs are `fn`s, so moduli and gaps evaluate. Remaining here: the diagonal completeness construction. Split out: [[creal-multiplication]], [[creal-order-and-bishop-bridge]].
- 2026-10-16: Writing data-carrying proofs as fns is a stopgap; [[theorem-witness-unfolding]] owns the real fix, and creal's fns become theorems again once it lands. Every `∃` elimination in creal restates its type by hand because of [[exists-proof-projection-type-not-reduced]].
- 2026-10-16: creal's data-carrying proofs are theorems again: [[theorem-witness-unfolding]] landed, so their witnesses compute without being `fn`s.
- 2026-10-17: Second round: products and `≤` (docs/creal-multiplication-round.md); [[creal-multiplication]] closed, the inverse split to [[creal-inverse]].
- 2026-10-17: Third round: the inverse of a real apart from zero (docs/creal-inverse-round.md); [[creal-inverse]] closed.
