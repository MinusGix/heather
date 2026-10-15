---
title: Build positive naturals and unreduced rational numbers
status: closed
labels: [stdlib,mathematics,arithmetic,setoids]
created: 2026-09-02
updated: 2026-10-14
---

Define a structurally positive denominator type and unreduced rational
representatives with integer numerators. Mathematical equality is
cross-multiplication equivalence; representation identity remains available.
This avoids making normalization, gcd, or non-structural termination a
prerequisite for rational arithmetic.

Implement embedding, signs/order, addition, multiplication, inverse under an
apartness/nonzero hypothesis, and respectfulness. Prove the equivalence laws
and ordered-field-facing facts needed by later real probes. Normalized
fractions may be a later representation connected by an isomorphism.

## What it assumes from elsewhere

- **[[setoid-core-api]]** owns explicit equality modulo representation.
- **[[cancellative-algebra-api]]** owns the cancellation lemmas needed by
  cross-multiplication.

## Log

- 2026-09-02: Filed as both useful arithmetic breadth and the first serious
  setoid customer.
- 2026-10-10: Landed (docs/setoid-rationals-round.md). `lib/std/pos.hthr` has `Pos` (positive by construction, `pred + 1`), `mul` and its value laws, and `Int` cancellation by a `Pos`. `lib/std/rat.hthr` has `Rat` = `Int` over `Pos`, unreduced; `≈` is cross-multiplication, with an `Equivalence` instance. It has `+`, `*`, `-` and a total `inv` respecting `≈` (`Respects2` instances for `+`/`*`); the commutative-ring laws, `x ≉ 0 → x·x⁻¹ ≈ 1`, and `≤` (preorder, antisymmetric modulo `≈`, total, respects `≈`, `+`-monotone, non-negative products); and the `ofInt` embedding (additive, multiplicative, injective, monotone). Client and controls: docs/showcase/rat_client.hthr and crates/elab/tests/lib_std_rat.rs. Residue goes to [[rational-order-completion]] (strict order, abs, monotone products, Archimedean). Normalized fractions as a second representation stay optional and are not filed.
- 2026-10-10: Whether the shifted `Pos` should stay is now [[positivity-evidence]] (docs/positivity-evidence-design.md).
- 2026-10-14: The shifted Pos is gone; Rat's denominator is Pos<Nat> sugar ([[retire-shifted-pos]]).
