---
title: Add cancellative algebra with explicit side conditions
status: closed
labels: [stdlib,mathematics,algebra,arithmetic]
area: mathematics
milestone: [math-classes]
created: 2026-09-02
updated: 2026-11-02
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
- 2026-11-02: Landed (`docs/ordered-algebra-design.md` §6). The distinction is carried by hypotheses: `OrderedAddMonoid::add_cancel_{l,r}` / `add_le_cancel_{l,r}` have no side condition; `OrderedSemiring::mul_cancel_pos_{l,r}` / `mul_le_cancel_pos_{l,r}` take `0 < z`; `OrderedRing::mul_cancel_apart_{l,r}` take `ApartBy(<, z, 0)`; `Nat::mul_cancel_{l,r}` and `Int::mul_cancel_{l,r}` take `¬(z = 0)` (plus `Int::mul_cancel_pos_l`, `Nat::pos_of_ne_zero`). No `Cancellative` class: every carrier here is an ordered monoid or a group, so it has no consumer; `List`'s `++` would be the first. The customer `OrderedSemiring::cross_same_trans` (a·d ≈ c·b, c·f ≈ e·d, 0 < d ⊢ a·f ≈ e·b) now proves `Rat::same_trans`. Probes at the end of `lib/_tests/std/algebra/ordered_field_tests.hthr`, with `¬` of unconditional multiplicative cancellation at `Nat` as the negative control.
