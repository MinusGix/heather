---
title: Prove the inverse's sign generically: positivity reflected by multiplication
status: open
labels: [stdlib,mathematics,reals,algebra,order]
created: 2026-10-19
updated: 2026-10-19
---

`OrderedField` (lib/std/ordered_field.hthr, docs/constructive-ordered-field-design.md) cannot derive that the inverse of a positive element is positive, nor the Archimedean property in its `inv_succ` form ("`0 < x` gives some `1/(k+1) < x`"). Both need multiplication to reflect positivity: `0 < x * y` and `0 < x` give `0 < y` (equivalently, strong extensionality of `*`: `x * y` apart from `x * z` gives `y` apart from `z`). That is a constructive axiom of its own, not a consequence of the interface's laws.

Prove it at both carriers (at `Rat` by `omega` on the cross-multiplied form; at `CReal` from the gap of `x * y` and the canonical bound of `x`), add it to `OrderedField` as a law, and derive generically: `inv_pos`, `inv_neg`, `inv_lt_inv` on positives, and `archimedean_inv`.

## What it assumes from elsewhere

- **[[constructive-ordered-field-interface]]** owns the class layers. Assumed here: only that `OrderedField` takes the inverse at `ApartBy(<, x, zero)` and has `mul_pos`.
