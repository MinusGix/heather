---
title: Exact intermediate value theorem for a locally non-constant function
status: closed
labels: [stdlib,mathematics,reals]
area: mathematics
milestone: [math-reals]
created: 2026-11-07
updated: 2026-11-07
---

`UnifContOn::ivt` (lib/std/analysis/closed_interval.hthr) finds an exact
root for a *strictly increasing* uniformly continuous function with
`f(a) <= 0 <= f(b)`, by a bisection in a `CauchyComplete` field
(docs/library/sequences-and-completeness.md §5). The general constructive form
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
- 2026-11-07: Done: `LocallyNonconstOn`, `UnifContOn::ivt_nonconst`, with
  `UnifContOn::ivt` (strictly increasing) now its corollary through
  `StrictMonoOn::nonconst`. The stages carry their nesting (`step` returns
  `l <= l2 ∧ r2 <= r`; `RootStage::nested_add`/`nested`), and every lower
  end past `N` lies in stage `N`. `step` is a `fn` over theorem pieces
  (`cut`, `keep_left`, `keep_right`): as one theorem the kernel ran out of
  fuel on `nested_add`. Probe: a root of `x³ - x` on `[-2, 2]` at CReal,
  local non-constancy from its third difference. The infimum route in an
  `OrderComplete` field was not needed and is not taken.
