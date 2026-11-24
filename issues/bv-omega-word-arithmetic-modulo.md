---
title: bv_omega: a low mask as a remainder, a borrowing subtraction modulo a power of two
status: open
labels: [tactics,bitvec]
area: tactics
created: 2026-11-24
updated: 2026-11-24
---

Found proving the word map's specification ([[runtime-hash-map-spec]],
`lib/native/runtime/word_map_laws.hthr`). A table of four slots probes with
`(j + 1).band(3)` and backward shifting tests `(j - i).band(3)`: both are
arithmetic modulo four on words, and `bv_omega` reads neither.

- **A low mask is read as a bound, not a remainder.** For
  `((j + 1).band(3)).toNat() = (j.toNat() + 1) % 4` with `j.toNat() < 4`,
  `bv_omega` adds `toNat(… & 3) <= 3` (`toNat_band_ofNat_le`) and stops with
  a model at `j = 3`. `BitVec::toNat_band_low_mask` says it exactly
  (`x.band(low_mask(k)).toNat() = x.toNat() % 2^k`); the proof states
  `ofNat(3) = low_mask(2)` by `refl` and cites it (`WordMap::band_three`).
- **A subtraction that may borrow is refused even where only its remainder is
  asked.** `((j - i).toNat()) % 4 = (j.toNat() + 4 - i.toNat()) % 4` is true
  for every `i, j < 4`; `bv_omega` answers "`j - i` may borrow; `omega` could
  not prove `toNat(i) <= toNat(j)`". The fact is
  `BitVec::toNat_sub_mod` (`(a + 2^n - b) % 2^n`).
- **`omega` overflows at `2^64`.** Given `toNat_sub_mod` with `pow(2, 64)`
  rewritten to its literal, `omega` stops with "coefficient overflow while
  multiplying coefficients". The proof goes round it with
  `Nat::mod_pow_mod` (the low two bits of the low sixty-four) so the literal
  only appears under `% 4` (`WordMap::slot_dist`).

## Wanted

`bv_omega` reads `x.band(2^k - 1)` as `x.toNat() % 2^k`, and `a - b` at a
width as `(a + 2^n - b) % 2^n` with the borrow a case of the division
variable rather than a refusal; `omega`'s coefficients are wide enough for
`2^64` times a small modulus (the arithmetic of every word fact).

## Log

- 2026-11-24: Proof tooling round (branch `claude/proof-tooling-omega`). Done:
  - A low mask reads as the remainder: `x & (2^k - 1)` at a literal width states `toNat(x) % 2^k` (`toNat_band_low_mask`) in place of the bound; a masked sum or difference is read through its wrap, `(toNat(a) + toNat(b)) % 2^k` and `(toNat(a) + 2^w - toNat(b)) % 2^k` (new `BitVec::toNat_band_low_mask_add`/`_sub` in `bitvec_shift_nat`), so the carry or borrow is a case of the remainder's quotient and the operation owes no side condition (docs/tactics/bv-omega-design.md §3.2). `WordMap::band_three` is gone, `next_slot` and `slot_dist` are `{ bv_omega }`.
  - `omega`'s Fourier–Motzkin step no longer overflows at a `2^64` coefficient beside a bound near `2^64`: it scaled the interval only to learn which sides exist (now read off the sign), and it combines bounds by their lcm, not their product.

  Left: a bare `a - b` that may borrow, with no mask, is still a side condition (the wrap is stated only under a low mask); and CutSat's own resolution still overflows 128 bits on `((j + 2^64 - i) % 2^64) % 4` once the real shadow has failed (it multiplies `2^64`-scale coefficients). The word map no longer meets either. Probes and controls: `lib/_tests/std/tactic/bitvec_omega_tests.hthr` ("Arithmetic modulo a power of two").
