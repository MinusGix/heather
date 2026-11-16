---
title: Points of the localic line are exactly the Cauchy reals
status: open
labels: [stdlib,mathematics,reals,locale-theory]
area: mathematics
milestone: [math-reals]
created: 2026-11-10
updated: 2026-11-10
---

`CReal::formal_point` (lib/std/locale/real_point.hthr) sends a Cauchy real to
a point of the line. Build the converse and the round trip, with no choice
principle: `Exists` is a Σ, so a point lying in a covered interval returns the
member it lies in (`FormalPoint::in_cover`).

## Plan

1. **Fine covers.** Every interval is covered by the intervals of width at
   most `e`, for any `0 < e`: `Split` iterated. By recursion on a number of
   steps `n` with `a.hi - a.lo <= (n + 1) * d`, gluing `(lo, hi - d)` with
   `(hi - 2d, hi)` (`RealLine::glue`), and `Rat::archimedean` for `n`.
2. **The sequence.** From `p: FormalPoint<QInterval>(…, in)`, start at the
   interval `p.some` gives, and at stage `n` read the member of the
   `2^-(n+1)`-fine cover the point lies in; take its lower end. Two stages'
   intervals meet in a nonempty one (`p.meets`, and `Shrink` makes members
   nonempty), so the ends differ by at most the larger width:
   `CReal::rounded`.
3. **Round trip.** `(real_of(p)).In(a) ↔ in(a)`, and
   `real_of(x.formal_point()) ≈ x`.
4. State the result as the first acceptance of [[real-presentation-comparison]]:
   the two maps, what they preserve (order, negation through
   `RealLine::negation`), and the assumption inventory, which should be empty.

Design: docs/library/localic-reals-design.md §5.

## What it assumes from elsewhere

- **[[localic-real-numbers]]** owns the presentation.
- **[[real-presentation-comparison]]** owns the comparison's statement shape.
