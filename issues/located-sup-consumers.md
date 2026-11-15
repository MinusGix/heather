---
title: Use located suprema for extrema of uniformly continuous functions and the IVT
status: closed
labels: [stdlib,mathematics,reals,order]
area: mathematics
milestone: [math-reals]
created: 2026-11-07
updated: 2026-11-07
---

The consumers [[order-completeness-located-sup]] named, left for a round of
their own. `OrderComplete` (lib/std/analysis/supremum.hthr) gives a
supremum for every inhabited, bounded-above, upper-located set.

- **Suprema of a uniformly continuous function on `[a, b]`.** The image
  `{f(x) | a <= x <= b}` is upper located: for `p < q`, take the modulus `δ`
  of `f` at `(q - p)/2` and a grid on `[a, b]` with spacing below `δ`;
  cotransitivity at each grid point says `f(xᵢ) > p` (an element above `p`)
  or `f(xᵢ) < (p + q)/2`, and if every grid point says the second, every `x`
  is within `δ` of one, so `f(x) <= q`. The grid walk and the covering lemma
  (each `x` in `[a, b]` is within `δ` of some grid point, found by
  cotransitivity against the grid, not by a floor) are the work. The result
  makes `BoundedOn` a theorem on a closed interval, where real_fn.hthr's
  product and chain rules take it as a hypothesis. Boundedness alone needs
  only the grid, not the supremum, so the bound may land first.
- **The intermediate value theorem with a located sign change.** The
  approximate form (for `f(a) < 0 < f(b)` and every `ε` some `x` with
  `|f(x)| <= ε`) is a bisection over cotransitivity and needs no
  completeness. An exact root needs more than continuity constructively
  (local non-constancy, or a located sign change on a subinterval), so the
  round decides which hypothesis to name first and states the approximate
  form beside it.

docs/library/sequences-and-completeness.md §3, §4.

## Log

- 2026-11-07: Filed from the located-suprema round.
- 2026-11-07: Done in lib/std/analysis/closed_interval.hthr
  (docs/library/sequences-and-completeness.md §5). One walk from `a` towards `b`,
  stepping `δ/2` while cotransitivity says `b - x > δ/2`, replaces the grid
  and its covering lemma; a point before or after a step is split by
  `StrictOrder::le_by_cases`, since the goals are `≤`. `UnifContOn::bounded`,
  `::located` (the image as `ImageOn`), `::sup` (OrderComplete),
  `::ivt_approx` (no completeness, read at `Rat`). The exact theorem names
  strict increase first (`StrictMonoOn`, `UnifContOn::ivt`, a bisection in a
  CauchyComplete field; `√2` at CReal in the probes). The locally
  non-constant form is [[ivt-locally-nonconstant]].
