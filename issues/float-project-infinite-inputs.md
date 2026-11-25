---
title: Project infinite inputs per saturation mode (P3109)
status: open
labels: [mathematics,floating-point]
area: mathematics
milestone: [math-float]
created: 2026-11-25
updated: 2026-11-25
---

`Format::project` (`lib/std/num/float/project.hthr`) projects an exact
rational. P3109's projection (interim report §4.7.5) also takes `±∞` and NaN,
and that is the only place `SatPropagate` differs from `SatFinite`: an
infinite input stays infinite under `SatPropagate` where the format has that
infinity, and clamps under `SatFinite`; under `SatNone` it stays infinite in
an extended domain and is NaN in a finite one. At an unsigned format `-∞`
is NaN under `SatNone` even toward zero or upward (the report's `X ≠ -∞`
exception), and clamps to 0 otherwise.

## The change

An input type of closed extended reals (`XFin(x)`, `±∞`, NaN) and
`project_ext`/`project_ext_unsigned` that send `XFin` to the existing
projections and the specials through the table above, with evaluation tests
per saturation mode. Operations on special-value operands already have their
tables in `arith.hthr`; this is the projection's half.

## What it assumes from elsewhere

- **`lib/std/num/float/project.hthr`** owns the projection of finite values
  (docs/library/float-p3109-design.md §6). Assumed here: only `sat_up`,
  `sat_down` and `unsigned_low`.
