---
title: P3109 square root and elementary functions
status: open
labels: [mathematics,floating-point]
area: mathematics
milestone: [math-float]
created: 2026-11-26
updated: 2026-11-26
---

The P3109 operations (`lib/std/num/float/p3109_ops.hthr`, design §8) cover
the operations whose exact value of finite operands is rational. Report
§4.10.8–§4.10.16 adds `Sqrt`, `Recip`, `RSqrt`, `Log`, `Exp`, the
trigonometric, hyperbolic and π-functions, `Softplus`, `Hypot`, `Atan2`: their
exact values are reals, so the projection has to round a real.

## The change

- `Sqrt`, `Recip` and `RSqrt` first: the library rounds a square root
  exactly (`arith.hthr`'s integer square root with a sticky bit, design
  §14.1 of floating-point-design.md), so their projection is that rounding
  plus `project_x`'s saturation and special values (`Sqrt(-x) = NaN`,
  `Sqrt(+∞) = +∞`).
- The elementary functions through `round_real.hthr`'s correct rounding of a
  `CReal` (apartness from the breakpoints) or its always-computable faithful
  rounding, per the report's accuracy requirements (§4.4, approximate
  implementations).

## What it assumes from elsewhere

- **[[float-p3109-operations]]** owns `project_x`, `Rnd` and the ω tables.
  Assumed here: only `project_x`'s handling of infinities and NaN.
