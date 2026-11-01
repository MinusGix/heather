---
title: A swapped rel_sym at an ordered field is reported as the wrong dictionary's assoc, at the statement
status: open
labels: [elab,diagnostics]
area: language
created: 2026-11-01
updated: 2026-11-01
---

Found while writing `difference::OrderedField::geometric_le` (issues/finite-difference-calculus.md).

In a `section<A: OrderedField(≈, <, <=, +, *)>`, a proof that passes
`A.rel_sym(a, b, h)` with its two endpoints swapped (so `h: b ≈ a` is given
where `a ≈ b` is wanted) is refused with

    this has type `(y: A) -> (z: A) -> (a: A) -> #op≈@0_0(#op+@0_3(#op+@0_3(y, z), a), …)`,
    but `(y: A) -> (z: A) -> (a: A) -> #op≈@0_0(#op*@0_4(#op*@0_4(y, z), a), …)` is expected here

located at the theorem's *statement*, not at the call. The message names the
additive `assoc` against the multiplicative one, which reads as an instance
resolution bug in the statement's `∏`; the real error is the swapped
argument order. Repro:

```heather
section<A: OrderedField(≈, <, <=, +, *)> {
theorem g1(x, q: A, i: Nat): x * ((∏ k < i, q) * q) ≈ (x * ∏ k < i, q) * q {
    A.rel_sym(x * ((∏ k < i, q) * q), (x * ∏ k < i, q) * q, A.multiplicative.assoc(x, ∏ k < i, q, q))
}
}
```

The same swap without the `∏` (plain `x * (p * q)`) is reported correctly, at
the call, with the two `≈` sides. So the fallback that retries the
mismatch is likely re-searching the `∏`'s `MonoidRel` dictionary and
reporting the last failed candidate.

Want: the mismatch reported at the `rel_sym` argument, with the two sides.
