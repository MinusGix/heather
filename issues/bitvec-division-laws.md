---
title: Prove the Euclidean laws of word division
status: closed
labels: [stdlib,mathematics]
area: mathematics
created: 2026-11-03
updated: 2026-11-06
---

`lib/std/bitvec/bitvec_div.hthr` (docs/fixed-width-integers-design.md §4)
defines `udivrem` by restoring long division and `sdiv`/`srem` over the
magnitudes. The probes (`lib/_tests/std/bitvec/bitvec_div_tests.hthr`) are
closed values only.

Wanted, at an open width:

- `a.toNat() = q.toNat() * d.toNat() + r.toNat()` and `r.toNat() < d.toNat()`
  for `d ≠ 0`, where `(q, r) = a.udivrem(d)`: by induction on the dividend's
  width over `division_step`, whose invariant is that the widened remainder is
  below the divisor;
- `x.udiv(0)` all ones and `x.urem(0) = x`;
- `a.toInt() = q.toInt() * d.toInt() + r.toInt()` for `sdiv`/`srem` away from
  `MIN / -1`, with `|r| < |d|` and `r`'s sign the dividend's.

These are what a verified lowering of `DIV`/`IDIV` would cite.

## Resolution (2026-11-06)

All three, in `lib/std/bitvec/bitvec_div.hthr` (design note §4.2):

- `BitVec::udivrem_spec`: `DivMod::Spec(a.toNat(), d.toNat(), …)` at every
  width and divisor, by induction on the dividend's width over
  `division_step`. The invariant is not "the widened remainder is below the
  divisor" but `DivMod::Spec` of the bits read so far, which also holds at a
  zero divisor; the remainder keeps its top bit zero because it is at most
  the dividend read so far. Corollaries `udiv_urem_toNat`, `urem_lt`.
- `BitVec::udiv_zero` (all ones) and `BitVec::urem_zero` (`x`).
- `BitVec::sdiv_srem_toInt` for `d ≠ 0` away from `MIN / -1` (a hypothesis
  on the readings: `¬(a.toInt() = -2^k ∧ d.toInt() = -1)`), with
  `srem_natAbs_lt` (`|r| < |d|`) and `srem_nonneg`/`srem_nonpos` (the
  remainder's sign is the dividend's); `srem_toInt` holds at every divisor.
  `SInt::div_rem_toInt`, `rem_natAbs_lt`, `rem_nonneg`, `rem_nonpos` restate
  them at `i64`.

The digit arithmetic is `DivMod::digit_keep`/`digit_take` in nat.hthr; the
sign/magnitude reading is `Int::of_sign` and `Int::of_sign_mul_add` in
int.hthr.
