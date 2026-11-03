---
title: Prove the Euclidean laws of word division
status: open
labels: [stdlib,mathematics]
area: mathematics
created: 2026-11-03
updated: 2026-11-03
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
