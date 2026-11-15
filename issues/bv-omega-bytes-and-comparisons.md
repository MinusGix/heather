---
title: bv_omega: byte extraction, unsigned comparisons and word equality goals
status: closed
labels: [proofs,bitvec,metaprogramming]
created: 2026-09-26
updated: 2026-09-28
---

`bv_omega`'s first slice (docs/tactics/bv-omega-design.md §4) takes words apart through
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

## Implemented 2026-09-28

The walk adds shared take/drop decompositions and both half-word ranges,
including nested extractions and definitions that step to either half.
Literal powers are emitted as coefficients. Unsigned Boolean equations in
scope become Nat orders; comparison and word equality goals use checked
bridge lemmas over a Nat `bv_omega` subgoal. Optional comparison operands
follow the existing careful retry policy for overflow and borrow.

`crates/elab/tests/bv_omega.rs` covers seven byte extractions, arithmetic
inputs, aliases, zero and open widths, both comparison outcomes and equation
orientations, word equality, and false-goal controls. Nested extraction also
required reconstructing both finite endpoints of positive Omega combinations
with a non-exact interval, using the existing endpoint lemmas.
