---
title: Factor decidable relations from evidence-producing comparison
status: open
labels: [stdlib,mathematics,order,decidability,design]
created: 2026-09-02
updated: 2026-09-02
---

Design the executable layer orthogonal to mathematical relation laws. Compare
pointwise `Decide<R(x,y)>`, a `DecidableRel(R)` dictionary, and a comparison
operation returning trichotomy evidence. Determine the eventual role of the
existing `Cmp` class and migrate nothing until its two consumers are accounted
for.

Acceptance should cover Boolean branching, `Nat`/`Int` comparison, generic
`min`/`max`, and a mathematical linear order deliberately lacking a decider.

## What it assumes from elsewhere

- **[[mathematical-order-hierarchy]]** owns order laws.
- **[[decide-class]]** owns proposition-level decision and its resolver story.

## Log

- 2026-09-02: Filed so decidability is an optional capability, never an order
  axiom.
