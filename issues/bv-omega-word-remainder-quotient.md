---
title: bv_omega does not know a word's remainder is below its divisor
status: open
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
