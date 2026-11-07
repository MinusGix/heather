---
title: Exact intermediate value theorem for a locally non-constant function
status: open
labels: [stdlib,mathematics,reals]
area: mathematics
milestone: [math-reals]
created: 2026-11-07
updated: 2026-11-07
---

`UnifContOn::ivt` (lib/std/analysis/closed_interval.hthr) finds an exact
root for a *strictly increasing* uniformly continuous function with
`f(a) <= 0 <= f(b)`, by a bisection in a `CauchyComplete` field
(docs/sequences-and-completeness.md §5). The general constructive form
(Bridges–Richman) asks less: `f` is *locally non-constant*, meaning every
`x < y` in `[a, b]` and every `c` have a `z` in `[x, y]` with `f(z)` apart
from `c`. That covers polynomials that are not constant, which strict
increase does not.

The bisection changes shape: a step cannot compare `f` at two fixed cut
points, so it asks local non-constancy for a point `z` in the middle third
with `f(z)` apart from `0`, and keeps the side the sign of `f(z)` says. The
stages no longer nest by monotonicity (`RootStage::le` used it), so the
proof carries the nesting itself (each stage inside the last). The
approximate theorem (`UnifContOn::ivt_approx`) needs none of this and stays
as it is.

A second route to try: the root as the infimum of `{x ∈ [a, b] | 0 < f(x)}`
in an `OrderComplete` field, which needs that set lower located, again from
local non-constancy.

## Log

- 2026-11-07: Filed from the located-sup-consumers round.
