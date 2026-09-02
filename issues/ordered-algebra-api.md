---
title: Connect ordered structures to addition and multiplication
status: open
labels: [stdlib,mathematics,order,algebra]
created: 2026-09-02
updated: 2026-09-02
---

Factor the compatibility laws between order and algebra: translation
invariance/monotonicity of addition, monotonicity of multiplication by a
nonnegative factor, positivity, and the ordered-ring/ordered-field composites
that real-number interfaces need.

Do not choose one giant `OrderedRing` prematurely. Probe which compatibility
theories are independently consumed by `Nat`, `Int`, rationals, absolute
value, and interval reasoning, and preserve constructive strict/non-strict
distinctions.

## What it assumes from elsewhere

- **[[mathematical-order-hierarchy]]** owns order laws.
- **[[semiring-ring-structure-api]]** owns ring laws.

## Log

- 2026-09-02: Filed as the bridge rather than folding order into the ring
  hierarchy itself.
