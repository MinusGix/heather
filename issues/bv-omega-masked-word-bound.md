---
title: bv_omega does not know a word masked by a literal is at most the mask
status: closed
labels: [proofs,bitvec,tactics]
area: tactics
created: 2026-11-13
updated: 2026-11-13
---

Found on the proof-carrying index round (PR #551): an index
into a ring of sixteen words is `i & 15`, and its bound

```heather
theorem ring_index(i: BitVec(64)): (i & 15).toNat() < 16 { bv_omega }
```

was refused. `bv_omega` takes a word apart through `add`, `sub`, `ofNat`,
`word_of_nat` and byte splits; any other word, `x & m` among them, is a leaf
whose only known bound is its range `< 2^n`, so `omega` sees an atom below
`2^64` and nothing below sixteen. The same bound is what every SHA-256
message-schedule read `W[(t - k) & 15]` needs.

## What it needs

- The law (beside [[bitvec-shift-mask-arithmetic]]'s), at every width: `(x & y).toNat() <= x.toNat()` and
  `<= y.toNat()` (a bit of `x & y` is set only where both are), and with a
  numeral mask `(x & ofNat(m)).toNat() <= m` (`toNat_ofNat_le` reads the
  literal past the width).
- `bv_omega` stating it for every `&` it meets under a `toNat`: a leaf whose
  word is `x.band(y)` gets the fact `toNat(x & y) <= toNat(y)` (or `<= m`
  when `y` is `ofNat(m)`) beside its range, for `omega` to read. A mask that
  is not a numeral still bounds, by the other word's `toNat`, which is then
  an atom of its own.

## Log

- 2026-11-13: fixed. `BitVec::toNat_band_le_left`, `toNat_band_le_right` and `toNat_band_ofNat_le` in `bitvec_nat`; `bv_omega` states the mask bound for a `band` leaf (`Walk::mask_bound`). Probes in `lib/_tests/std/tactic/bitvec_omega_tests.hthr`.
