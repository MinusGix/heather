---
title: Located suprema as an order-completeness capability
status: closed
labels: [stdlib,mathematics,reals,order]
area: mathematics
milestone: [math-reals]
created: 2026-11-06
updated: 2026-11-07
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
- 2026-11-07: Done. lib/std/analysis/supremum.hthr: `UpperBound`, `IsSup`
  (unique, respects, below every upper bound), `UpperLocated`, and
  `IsSup::located` (a supremum makes the set located, so the hypothesis is
  exactly right). `CauchyComplete::located_sup` by bisection at rate 3/4
  over plain-parameter stages (`Bisection::*`); the `OrderComplete` class;
  and the converse `OrderComplete::cauchy_limit`, so the two capabilities
  are equivalent over an ordered field. `CReal` instance in
  real_complete.hthr; probes in lib/_tests/std/analysis/supremum_tests.hthr
  (the ray below `c` has supremum `c`, found at `CReal`, refused at `Rat`).
  The consumers moved to [[located-sup-consumers]]; the merged-call kernel
  panic hit on the way is [[merged-call-through-upcast-panics]].
  docs/sequences-and-completeness.md §4.
