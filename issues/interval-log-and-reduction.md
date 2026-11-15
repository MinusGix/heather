---
title: Argument reduction for exp, sin, cos, and log by atanh, in the CReal interval checker
status: open
labels: [reals,intervals,float]
area: mathematics
created: 2026-10-27
updated: 2026-11-01
---

`CReal::exp_rat`, `sin_rat` and `cos_rat` (`lib/std/num/float/elementary.hthr`,
`docs/library/floating-point-design.md` §16, "Series and elementary functions") sum
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

## Log

- 2026-10-31: 2026-10-31: log at positive rationals landed by the binade reduction (`Binade::of`, log 2 = 2·atanh(1/3)) and is an `Enclosed` leaf through `RealExpr::enclosed` ([[creal-compress-and-transcendentals]]); its statement as exp's inverse stays open. exp's halving reduction and sin/cos range reduction are still open here.
- 2026-11-01: sin and cos reduce by halving, not by π. The leaves scale x by 2^-k, k = width of its bound, enclose sin and cos there and double back k times by the addition laws on intervals (`CReal::trig_reduced`, elementary_real.hthr). `sin(10)`, `cos(10)`, `sin(30)` and `cos(100)` close by `intervals()`.
  - Two costs had to go first. The Lipschitz modulus grew like exp(2B); it is now a constant 2·exp_reach(1), from |sin|, |cos| <= 1 (trig_law.hthr). The base series also ran at a term read at 2^-57 that still carried its trailing zero bits; it now runs at the term after `Dyadic::trim`.
  - `sin(1000)` does not close at the default precision.
  - Left here: π reduction for sin and cos, which would cut the doublings, and exp's halving reduction.
