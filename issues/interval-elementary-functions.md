---
title: Interval enclosures of exp, log and sin by series with remainder bounds
status: closed
labels: [reals,intervals,float]
area: mathematics
created: 2026-10-26
updated: 2026-10-27
---

Interval enclosures of `exp`, `log`, `sin` and friends at a precision, by
Taylor series with a remainder bound, over `Interval`
(`lib/std/num/float/interval.hthr`). This is CoqInterval's next layer
(`docs/coq-hardware-floats-survey.md` §6.1) and the enclosure that
`float-transcendental`'s Ziv loop refines until it misses every rounding
breakpoint (`docs/floating-point-design.md` §6): correctly rounded `exp`
is a refinement of `exp`'s enclosure plus an apartness proof.

Shape: argument reduction (`exp(x) = exp(x/2^k)^(2^k)`), a partial sum
evaluated in interval arithmetic, and a remainder interval
`[0, |x|^(n+1)/(n+1)! · bound]` added on; the containment theorem is stated
against the real function, so it needs the function at `CReal`
(`real-functions-and-derivatives`) or a series definition at `Rat` for
rational arguments first.

## What it assumes from elsewhere
- **[[dyadic-interval-enclosures]]** (closed) owns `Interval`. Assumed
  here: only the arithmetic's containment theorems.
- **[[interval-creal-enclosures]]** owns containment at `CReal`, which a
  statement about the real `exp` needs.

## Log

- 2026-10-27: LANDED (design `docs/floating-point-design.md` §16, "Series and
  elementary functions"). `lib/std/num/float/series.hthr`: a `Series` with
  ratios at most 1/2 past `start`, the tail and decay bounds, its limit as a
  `CReal` (`Series::real`, index `start + width(scale·(n+1) + n)` by
  `Nat::le_ones_width`), within `2|t_N|` of every partial sum past `start`,
  and its enclosure from interval term and sum, widened by twice the last
  term and stopped once that is below `2^-p` (`Series::settle`).
  `lib/std/num/float/elementary.hthr`: `CReal::exp_rat`, `sin_rat`, `cos_rat`
  at rationals, `start` from `Rat::abs_ceil`, exact at zero. The checker's
  `RBox(Enclosed)` leaf carries a real with its own enclosures; the tactic
  reads the three heads. Shipped as a series definition at `Rat` (the issue's
  second route): the functions at real arguments and their laws are
  `elementary-functions-at-reals`, `log` and argument reduction
  `interval-log-and-reduction`.
