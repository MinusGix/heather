---
title: Located suprema as an order-completeness capability
status: open
labels: [stdlib,mathematics,reals,order]
area: mathematics
milestone: [math-reals]
created: 2026-11-06
updated: 2026-11-06
---

The order-completeness side of [[real-completeness-interfaces]]. A supremum
exists constructively only for a set whose upper bounds are located: for
`a < b`, either `b` bounds the set or some element exceeds `a`. State that
as a capability `OrderComplete` beside `CauchyComplete`
(lib/std/analysis/sequence.hthr). Prove that every `CauchyComplete` field
inhabits it: with the located disjunction as data, bisection gives a Cauchy
sequence of upper bounds whose limit is the supremum, with no choice.

Consumers to try: the intermediate value theorem for a uniformly continuous
function with a located sign change, and suprema of `UnifContOn` functions
on a closed interval, which make `BoundedOn` a theorem there instead of a
hypothesis (real_fn.hthr's product and chain rules take it as a hypothesis).

The unrestricted least-upper-bound principle implies LPO, so it is not a
capability any constructive carrier has. Record that as a ¬ statement only if
an LPO-shaped principle is ever named in the library.

docs/sequences-and-completeness.md §2 has the table of notions.

## Log

- 2026-11-06: Filed from the sequences round.
