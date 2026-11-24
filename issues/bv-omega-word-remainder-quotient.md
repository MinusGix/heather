---
title: bv_omega does not know a word's remainder is below its divisor
status: closed
labels: [proofs,bitvec,tactics]
area: tactics
created: 2026-11-24
updated: 2026-11-24
---

Found on the runtime ports ledger (docs/native/dogfooding-plan.md §5.1): a
hash table's slot is `hash % capacity`, and its index bound

```heather
runtime fn port_word_slot(mut t: [u64; 8], k: u64) → u64 { t[k % 8] := k; 0 }
```

was refused: "`put`'s `inside` was left to its default, which did not give
`∥toNat(urem(k, ofNat(8))) < 8∥` … `omega` got stuck … left as atoms by a
bound [`toNat(urem(k, ofNat(8)))` did not compute within 4096 steps]".
`bv_omega` took a word apart through `add`, `sub`, `ofNat`, `word_of_nat`,
byte splits, `&`, `zero_extend` and `>> k`; `BitVec::urem` and
`BitVec::udiv` (`lib/std/bitvec/bitvec_div.hthr`) were leaves known only by
their range `< 2^n`.

## What it needs

- The laws over the words' values, at every width and divisor, from
  `BitVec::udivrem_spec` ([[bitvec-division-laws]]): `x % d <= x`;
  `x % d < d` and `x / d <= x` away from a zero divisor; over a divisor of
  known value `c`, `x % d < c`, `q * c <= x < q * c + c` and the link
  `x = q * c + r`.
- `bv_omega` stating them beside a `urem`/`udiv` leaf, as it states the mask
  bound beside a `band` ([[bv-omega-masked-word-bound]]), with a divisor
  that is not a literal known positive from a test on the path (`0 < n`,
  `n ≠ 0`).

## Log

- 2026-11-24: fixed. Lemmas in `bitvec_div`: `toNat_urem_le`,
  `toNat_urem_lt_or`, `toNat_udiv_le_or`, and over a divisor of known value
  `toNat_urem_lt_value`, `toNat_udiv_mul_le_value`, `toNat_udiv_lt_value`,
  `udiv_urem_value`; `bitvec_omega::toNat_ne_of_ne`. `bv_omega` keeps
  `x % d` and `x / d` as leaves and states those facts beside them
  (`Walk::division_value`; docs/tactics/bv-omega-design.md §3.1), reading
  `ofNat(c)` of a literal within a literal width as `c` and any other
  divisor through the disjunctions, which `omega` splits only on need; a
  disequation `n ≠ 0` in scope is now read like the other comparisons.
  Probes and negative controls in
  `lib/_tests/std/tactic/bitvec_omega_tests.hthr` (`rem_*`, `div_*`). Left:
  the link `x = q * d + r` over a divisor that is not a literal (a product
  of atoms; a word goal spells it as a word `mul`, which the walk does not
  take apart). The Nat analogue in `omega` is
  [[omega-nonliteral-div-mod-facts]]. On the way: a fit over no atoms at an
  open width (`ofNat(0)`'s `0 < 2^w`) was proved by `trivial`; it goes to
  `omega` now.
