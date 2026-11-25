---
title: bv_omega does not read a negated order of words, ¬(a <= b)
status: closed
labels: [tactics,bitvec]
area: tactics
created: 2026-11-25
updated: 2026-11-25
---

Met proving `window_fits_false` (`lib/native/runtime/word_fits.hthr`, [[bv-omega-fits-through-wrapping-sum]]): with `over: ¬(base <= limit - len)` and `room: len <= limit` in scope, `bv_omega` does not prove `limit.toNat() < base.toNat() + len.toNat()`. It reads a negated equation of words (`d ≠ 0`, `negated_word_fact`) but not a negated order: `¬(a <= b)` and `¬(a < b)` at a word are left out, so the subtraction's value never meets the fact. The proof decides the comparison at the values instead (`Nat::le_dec(base.toNat(), (limit - len).toNat())`, then `omega` to `(limit - len).toNat() < base.toNat()`).

## Wanted

`negated_word_fact` also reads `¬(a <= b)` as `toNat(b) < toNat(a)` and `¬(a < b)` as `toNat(b) <= toNat(a)` (a lemma each in `bitvec_omega`, from `unsigned_le_prop`/`unsigned_lt_prop` and Nat's trichotomy), so the else-branch of an `if h: a <= b` reads as the then-branch does. Then `window_fits_false`'s inner `le_dec` goes.

## Log

- 2026-11-25: Fixed the same round: `negated_word_fact` reads `¬(a <= b)` as `toNat(b) < toNat(a)` and `¬(a < b)` as `toNat(b) <= toNat(a)` through `bitvec_omega::unsigned_not_le_prop`/`unsigned_not_lt_prop`. `window_fits_false` reads its negated test directly; probes `not_le_prop`, `not_lt_prop`, `not_le_sub` in `lib/_tests/std/tactic/bitvec_omega_tests.hthr`.
