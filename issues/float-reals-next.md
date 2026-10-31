---
title: Finish float-reals - signed error at the reals, roots of reals, ordered-field transfer, faithful rounding
status: open
labels: [mathematics,reals,float]
area: mathematics
milestone: [float-reals]
created: 2026-10-31
updated: 2026-10-31
---

What [[float-reals-sqrt-and-error]] left of `float-reals`
(docs/floating-point-design.md §6, §17), in rough order of use:

- **The error model at a real of either sign.** `Format::real_error_nonneg`
  and `real_relative_nonneg` take `0 ≤ x`. Whether `x ≥ 0` cannot be
  decided, but the conclusion is a `≤` (a negation at `CReal`), so
  `CReal::le_by_sign` can split on it; the negative side wants
  `RoundsToReal` of `-x` under the conjugate mode (`rounds_neg` at the
  reals) and `|x| ≈ -x` for `x ≤ 0`.
- **The root as a product.** `CReal::sqrt_rat(q) * CReal::sqrt_rat(q) ≈
  |q|`, and that `IsSqrt` determines its real up to `≈` (two cuts of one
  rational agree; needs a rational strictly between two apart reals, which
  `CReal::Lt`'s witness gives). Neither was needed for the float theorems,
  which read the root only through comparisons.
- **The root of a real**, not just a rational: `√` is Hölder-½, so the
  term index for `2^-n` is about `2n`; the customer is error analysis of
  compound expressions (`√(a² + b²)`).
- **The transfer to any ordered field** of §5.1/§6 (`RoundsTo` over `K`,
  with `CReal` an instance), **faithful rounding** that always computes, and
  `Placed`. Every statement in float_real.hthr is at `CReal`; the ordered
  field version would let `Rat` and `CReal` share them.
