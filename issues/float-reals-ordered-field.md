---
title: Floats over any ordered field - RoundsTo over K, faithful rounding, Placed
status: open
labels: [mathematics,reals,float]
area: mathematics
milestone: [float-reals]
created: 2026-10-31
updated: 2026-10-31
---

The last item of `float-reals` (docs/floating-point-design.md §5.1, §6),
split from [[float-reals-next]] when its other three items landed.

Every statement in `lib/std/num/float/float_real.hthr` is at `CReal`, and
the error model there is proved twice over: once at `Rat` (error.hthr), once
at the reals through the cut of a rounding interval (`Format::real_error`
and the rest). The design's plan is one statement over any ordered field
`K` (`RoundsTo` over `K`, with `Rat` and `CReal` instances), so that the
two share their theorems, plus:

- **Faithful rounding that always computes**: at a real, return one of the
  two neighbours of an enclosure, with no breakpoint to decide, so it ends
  without the Padé gap of [[exp-log-grid-gap]].
- **`Placed`** (§6): the real's position against the grid, read off an
  enclosure that clears every breakpoint.

## Done when

- `RoundsTo` and the error model stated once over an ordered field, with the
  `Rat` and `CReal` theorems as instances, or a recorded decision that the
  duplication is cheaper to keep, with its reason.
- A faithful rounding of an `Enclosed` real that always returns, with its
  theorem, and a probe at a transcendental.
