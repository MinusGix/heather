---
title: Prove Ziv's search ends from apartness from the breakpoints (Padé gap for exp and log)
status: open
labels: [mathematics,reals,float]
area: mathematics
milestone: [float-reals, float-transcendental]
created: 2026-10-31
updated: 2026-10-31
---

`Format::round_real` (lib/std/num/float/round_real.hthr) is Ziv's search with
fuel: it returns a float only with its `RoundsToReal` proof, and `None` when
the tries run out. Nothing yet says enough tries always succeed. That is
the `float-reals` statement of docs/floating-point-design.md §6: correct
rounding computes from apartness from the breakpoints.

Scope:

- `F.Breakpoint(mode, b)` for a rational `b` (a representable value for the
  directed modes, a midpoint for the nearest modes, plus the overflow
  threshold), and `F.Placed(x)` / apartness of `x` from every breakpoint near
  it, as §6 states them;
- a theorem that an enclosure narrower than the gap rounds to one float at
  both ends, so `round_enclosed` returns `Some` within a computable number of
  tries; from it a total `round_real_apart(F, mode, x, apart)` with no
  `Option`;
- for exp and log, the gap itself: flean's `ExpTermination.lean` bounds
  `|exp(x)·2^s - m|` away from zero by Padé approximants, which is exactly an
  apartness proof from the breakpoints at a dyadic argument other than zero
  (`exp(0) = 1` is a breakpoint and needs its own case).

## What it assumes from elsewhere
- **[[creal-compress-and-transcendentals]]** (closed) owns the search and its
  correctness. Assumed here: only that a refinement step narrows every
  enclosure by a fixed factor, which the series enclosures do in `p`.
