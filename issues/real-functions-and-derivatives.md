---
title: Real functions, Lipschitz bounds and a constructive derivative
status: open
labels: [stdlib,mathematics,constructive]
area: mathematics
milestone: [math-reals]
created: 2026-10-21
updated: 2026-10-21
---

Functions on `CReal` with a modulus of continuity, Lipschitz bounds, and a
constructive derivative (Bishop-style uniform differentiability is the
obvious candidate; compare a derivative on an abstract ordered field), with
the chain rule and derivatives of polynomials. Then `exp`, `log`, `tanh`
and `sqrt` as real functions with their laws and derivatives.

Customers: ML smoothness and descent (`docs/wick-survey.md` §4.1, §3.5),
activation functions, the float library's transcendental specifications. A
formal derivative on polynomials is enough for the first ML round, so this
can proceed at its own pace.

## What it assumes from elsewhere

- **[[real-completeness-interfaces]]** owns completeness. Assumed here: only
  that limits of regular sequences are available where the elementary
  functions need them.

## Log
