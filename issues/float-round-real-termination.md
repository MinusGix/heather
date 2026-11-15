---
title: Prove Ziv's search ends from apartness from the breakpoints (Padé gap for exp and log)
status: closed
labels: [mathematics,reals,float]
area: mathematics
milestone: [float-reals, float-transcendental]
created: 2026-10-31
updated: 2026-10-31
---

`Format::round_real` (lib/std/num/float/round_real.hthr) is Ziv's search with
fuel: it returns a float only with its `RoundsToReal` proof, and `None` when
the tries run out. Nothing yet says enough tries always succeed. That is
the `float-reals` statement of docs/library/floating-point-design.md §6: correct
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

## Log

- 2026-10-31: LANDED the search's end (docs/library/creal.md,
  "The search ends"). `F.Cell(x, h, k)` / `F.OffGrid(x)` state the gap against
  the half-unit grid, which holds every breakpoint of every mode. That is
  stronger than per-mode `Breakpoint`, and it needs no case split.
  `Enclosed::Narrows` is the narrowing hypothesis. `round_enclosed_ends`
  proves the search answers within `round_apart_tries`. `round_real_apart`
  is total, with `round_real_apart_correct`. `CReal::enclosed_narrows` is the
  first instance, and 1/3 at binary32 computes by `refl`. The Padé gap for
  exp and log, and narrowing of their series boxes, moved to
  [[exp-log-grid-gap]]. Per-mode `Breakpoint`/`Placed` were not built, since
  nothing needs them yet (decision recorded in the doc).
