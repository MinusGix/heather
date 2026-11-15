---
title: Finish float-reals - signed error at the reals, roots of reals
status: closed
labels: [mathematics,reals,float]
area: mathematics
milestone: [float-reals]
created: 2026-10-31
updated: 2026-10-31
---

What [[float-reals-sqrt-and-error]] left of `float-reals`
(docs/library/floating-point-design.md §6, §17), in rough order of use:

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

## Resolution (2026-10-31)

The first three items landed (design §17.1–§17.3); the fourth moved to
[[float-reals-ordered-field]].

- **Signed error.** `Format::real_error` (`|r - x| <= u·|x| + η` while
  `|x| <= M`) and `real_relative` (`|r - x| <= u·|x|` while `m <= |x| <= M`)
  at every real, split by `CReal::le_by_sign` inside the `≤`. The
  nonpositive side needed no conjugate mode: it cuts the rounding interval
  to `[-M, 0]` (or `[-M, -m]`) and reads the rational bound at its ends
  through `CReal::err_between_nonpos`. New at `CReal`: `le_abs`,
  `neg_le_abs`, `abs_nonneg`, `abs_of_nonneg`, `abs_of_nonpos`.
- **The root as a product, and uniqueness.** `CReal::rat_between` (a
  rational strictly between two apart reals) gives `is_sqrt_unique` and
  `is_sqrt_sq` (`s * s ≈ x` from the cut, with `Rat::root_floor_up` and
  `root_floor_down`: the roots from below approach `|q|` from each side),
  hence `CReal::sqrt_rat_sq`.
- **The root of a real.** `CReal::sqrt(x)` is `√|x|`; its n-th term is
  `root_floor(x.at(2n+4), n+2)`, regular because `p² <= |b| + d²` puts `p`
  under `b`'s root plus `d` (`Rat::lt_root_floor_add`). `CReal::IsRoot` is
  the cut at a real argument: `sqrt_is_root`, `is_root_sq`, `sqrt_sq`
  (`√x·√x ≈ |x|`), `sqrt_nonneg`, `sqrt_respects`, `sqrt_ofRat` (it is
  `sqrt_rat` at a rational), and `Finite::sqrt_rounds_root` at a float.
  `√(3² + 4²) ≈ 5` is a probe.
