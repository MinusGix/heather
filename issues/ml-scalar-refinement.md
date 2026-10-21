---
title: One model at Rat, CReal and Float with a composed error theorem
status: open
labels: [design,machine-learning,floating-point]
area: machine-learning
created: 2026-10-21
updated: 2026-10-21
---

The ML area's float story (`docs/wick-survey.md` §3.1). A model is written
once over a scalar class and instantiated at `Rat` (exact, runs, decides
concrete facts), `CReal` (the specification) and `Float(F)` (the
implementation, rounding chosen per operation, summation order explicit).
The link is a per-layer error theorem `|float x − real x| ≤ ε` that composes
along the layer grammar like a Lipschitz bound. Wick's architecture review
reached the same position ("floats are not a scalar", `ARCHITECTURE.md`
§2.6) and never built it; its `FloatR` instances are `sorry`.

Done when one small network's forward pass has such a composed bound, for at
least binary32 and one low-precision format (E4M3 or bfloat16), stated per
format. Look at Wisp's drift theorems for linear and MLP chains first.

## What it assumes from elsewhere

- **[[floating-point-formalization]]** owns floats. Assumed here: the
  standard model with γ-composition (`float-error`) and the arithmetic
  theorems (`float-arith`).
- **[[ml-layers-reverse-mode]]** owns the layer grammar.

## Log
