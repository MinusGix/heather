---
title: Prove the inverse's sign generically: positivity reflected by multiplication
status: closed
labels: [stdlib,mathematics,reals,algebra,order]
created: 2026-10-19
updated: 2026-10-20
---

`OrderedField` (lib/std/algebra/ordered_field.hthr, docs/library/constructive-ordered-field-design.md) cannot derive that the inverse of a positive element is positive, nor the Archimedean property in its `inv_succ` form ("`0 < x` gives some `1/(k+1) < x`"). Both need multiplication to reflect positivity: `0 < x * y` and `0 < x` give `0 < y` (equivalently, strong extensionality of `*`: `x * y` apart from `x * z` gives `y` apart from `z`). That is a constructive axiom of its own, not a consequence of the interface's laws.

Prove it at both carriers (at `Rat` by `omega` on the cross-multiplied form; at `CReal` from the gap of `x * y` and the canonical bound of `x`), add it to `OrderedField` as a law, and derive generically: `inv_pos`, `inv_neg`, `inv_lt_inv` on positives, and `archimedean_inv`.

## What it assumes from elsewhere

- **[[constructive-ordered-field-interface]]** owns the class layers. Assumed here: only that `OrderedField` takes the inverse at `ApartBy(<, x, zero)` and has `mul_pos`.

## Log

- 2026-10-20: LANDED. `OrderedField` has the law `pos_of_mul_pos` (`0 < x`, `0 < x * y` give `0 < y`). `Rat` proves it by refuting `y ≤ 0`, since it decides `≤`; no `omega` on the cross-multiplied form was needed. `CReal` builds the gap at one far index of the product (`Rat::le_of_mul_le_bounded` with the canonical bound of `x`, then `lt_of_term`). Derived generically in `lib/std/algebra/ordered_field.hthr`: `inv_pos`, `inv_neg`, `inv_inv`, `inv_lt_inv` (on positives), `archimedean_inv` (`0 < x` gives some `inv(of_nat(n+1)) < x`), with the helpers `of_nat_pos`, `neg_mul`, `neg_mul_neg`, `OrderedAddGroup::neg_pos`, `neg_of_neg_pos`. The client calls them at both carriers with `x⁻¹` notation. Design: docs/library/constructive-ordered-field-design.md, "The inverse's sign".
