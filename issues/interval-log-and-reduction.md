---
title: Argument reduction for exp, sin, cos, and log by atanh, in the CReal interval checker
status: open
labels: [reals,intervals,float]
area: mathematics
created: 2026-10-27
updated: 2026-10-27
---

`CReal::exp_rat`, `sin_rat` and `cos_rat` (`lib/std/num/float/elementary.hthr`,
`docs/floating-point-design.md` §16, "Series and elementary functions") sum
their series from `start`, the point past which each ratio is at most 1/2:
twice `⌊|a|⌋ + 1` for exp and once for sin and cos. The enclosure therefore
costs a step per unit of the argument before it starts to converge, and the
term at `start` can be large (`exp(100)` starts near `2^80`), which `Series::settle`
pays for in more steps. There is no `log` yet.

Scope:

- argument reduction for exp, `exp(a) = exp(a / 2^k)^(2^k)`, as an
  `Enclosed` leaf whose enclosure is the power of the reduced series'
  (`Interval::pow_has_real`), with the identity proved at `CReal`; it needs
  `exp(a + b) ≈ exp(a) · exp(b)` at rationals, or at least the halving case;
- range reduction for sin and cos by multiples of π/2, which needs π as a
  real with an enclosure (Machin's formula from an atan series is the usual
  route);
- `log` at positive rationals by the atanh series,
  `log(x) = 2 · atanh((x - 1)/(x + 1))`, after reducing `x` by powers of two
  (`log(x · 2^k) = log(x) + k · log 2`), stated against a real `log` that is
  `exp`'s inverse, so it waits for that law too.

## What it assumes from elsewhere
- **[[interval-elementary-functions]]** (closed) owns `Series`, the three
  functions at rationals, and the `RBox` leaf.
- **[[elementary-functions-at-reals]]** owns the functional equations the
  reductions need.
