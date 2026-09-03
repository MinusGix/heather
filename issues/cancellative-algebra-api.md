---
title: Add cancellative algebra with explicit side conditions
status: open
labels: [stdlib,mathematics,algebra,arithmetic]
created: 2026-09-02
updated: 2026-09-02
---

Develop left/right additive cancellation and multiplication cancellation under
nonzero or positivity hypotheses. The API must distinguish an unconditional
cancellative operation from the integral-domain-shaped theorem needed to
cancel a nonzero factor.

The forcing customer is transitivity of cross-multiplication equality for
unreduced positive-denominator rationals. `Nat` and `Int` provide the concrete
controls; avoid proving a hierarchy with no consumer.

## What it assumes from elsewhere

- **[[semiring-ring-structure-api]]** owns the surrounding two-operation laws.
- **[[positive-naturals-and-rationals]]** owns the rational representation.

## Log

- 2026-09-02: Filed because the current integer API has multiplication
  monotonicity but no multiplication-cancellation kit.
