---
title: bv_omega: byte extraction, unsigned comparisons and word equality goals
status: open
labels: [proofs,bitvec,metaprogramming]
created: 2026-09-26
updated: 2026-09-26
---

`bv_omega`'s first slice (docs/bv-omega-design.md §4) takes words apart through
`add`, `sub`, `ofNat`, `word_of_nat` and the definitions that step to them.
`lib/decimal_line.hthr` still does three kinds of word step by hand:

- byte extraction: 7 uses of `bitvec_nat::toNat_take_drop` in `word_bytes_of`.
  The row would state `x.toNat() = lo.toNat() + 2^k * hi.toNat()` for
  `take_low`/`drop_low` and add `toNat_lt_pow` for each half.
- unsigned comparison: `unsigned_lt_nat` in `below_value` and `place_step`,
  where a Bool equation `a.unsigned_lt_bit(b) = True/False` becomes a Nat
  order.
- word equality goals: `a = b` at `BitVec(n)` through `ofNat_toNat`, reduced to
  a `toNat` equation.

Each is a new row in the walk's table (§3) over the same fact form
`t.toNat() + q = p`.

## What it assumes from elsewhere

- **[[bitvec-nat-lifting-tactic]]** owns the tactic and its emission shape.
  Assumed here: only the fact form and the bundle.
