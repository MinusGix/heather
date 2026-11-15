---
title: Read x ^ n at a literal exponent in ring and nlinarith
status: closed
labels: [proofs,solver,arithmetic]
area: tactics
milestone: [tac-arith]
created: 2026-11-06
updated: 2026-11-06
---

`ring` reads `Rat::pow`/`CReal::pow` (`x ^ n` at an `Int` exponent) as an
atom, so `x ^ 2 ≈ x * x` is not `ring`'s, and `nlinarith` does not see
`x ^ 2` as a square (its squares are the `t * t` the problem shows):

```heather
theorem t(b: Rat): b ^ 2 ≈ b * b { ring }            // refused
theorem t(b: Rat): 0 < b ^ 2 + 1 { nlinarith }        // refused
```

The division round (docs/library/division-design.md) added a sign rule
`Rat::nonneg_sq` so a divisor `b ^ 2 + 1` is found, but the tactics still
miss it. Wanted: at a literal `OfNat(k)` exponent, read `x ^ OfNat(k)` as
`x.npow(k)`, i.e. `x` multiplied `k` times (`pow_ofNat` is `refl`,
`npow` is `1 * x * … * x`), and at a negative literal as the power of
`x⁻¹` with its reciprocal fact. `nlinarith`'s squares
(`FieldReading::squares`) should then record `x ^ 2`'s base.

## Log

- 2026-11-06: Done: `Reifier::literal_power` reads `x ^ k` at a literal exponent (up to 16) as `1 * x * … * x`, and at a negative literal as the power of `x⁻¹` at the power's proof; `nlinarith` sees `x ^ 2` as a square (probes in ring_field_tests and linarith_tests).
