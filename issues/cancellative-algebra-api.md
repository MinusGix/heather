---
title: Add cancellative algebra with explicit side conditions
status: open
labels: [stdlib,mathematics,algebra,arithmetic]
area: mathematics
milestone: [math-classes]
created: 2026-09-02
updated: 2026-10-14
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
- 2026-10-10: Customer slice from the rationals round. `Int::mul_cancel_pos_r` and `Int::mul_le_cancel_pos_r` (lib/std/pos.hthr) cancel a right factor given as a `Pos`, so the side condition is carried by the type. A `Nat` multiplicative cancellation still does not exist, and neither do left-factor or `≠ 0` forms.
- 2026-10-14: Int::mul_cancel_pos_r and Int::mul_le_cancel_pos_r moved to lib/std/num/rat.hthr and take p: Pos<Int> ([[retire-shifted-pos]]).
