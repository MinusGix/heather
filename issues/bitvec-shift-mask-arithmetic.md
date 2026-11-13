---
title: Shifts and low masks of a word as arithmetic on toNat
status: closed
labels: [bitvec,library,native]
area: heather-in-heather
milestone: [nh-library]
created: 2026-11-12
updated: 2026-11-12
---

Nothing says what a shift or a low mask of a word is as arithmetic on its `toNat` (2026-11-12). `lib/std/bitvec/bitvec_nat.hthr` has `toNat` of `add`, `mul`, `neg` and `sub` modulo `2^n`; the shifts and `band` have bit-level laws only (`bitvec.hthr`, `bitvec_resize.hthr`, `bitvec_rotate.hthr`).

Customers: a layout computed by compiled code (`docs/layout-design.md` §4) rounds a size up to a power-of-two alignment as `n + ((0 - n) & (a - 1))`, and its agreement theorem with `Nat::round_up` is exactly these laws. The arena's cell arithmetic, the lexer's packed token word ([[scan-token-word-packing-unproved]]) and any index scaled by a shift (`(t << 2) + 64` in `sha256_block.hthr`) read the same facts, today each by `bv_decide` at closed widths or not at all.

## The laws

For `x: BitVec(n)` and `k <= n`, each stated with neutral `n` and `k` and proved once:

- `x.shift_left(k).toNat() = (x.toNat() * 2^k).mod(2^n)`, and the form without the `mod` where `x.toNat() * 2^k < 2^n`.
- `x.shift_right(k).toNat() = x.toNat().div(2^k)`.
- A low mask: `BitVec::low_mask(k)` (or the existing spelling, if one is there) with `toNat() = 2^k - 1`, equal to `BitVec::ofNat(2^k) - 1` for `k < n`, and `x.band(low_mask(k)).toNat() = x.toNat().mod(2^k)`.
- `x.band(low_mask(k).complement()).toNat() = x.toNat() - x.toNat().mod(2^k)`: rounding down to a multiple of `2^k`.
- The pair as one statement, `x = (x >> k << k) | (x & low_mask(k))`, if it falls out.

`bv_omega` learning the two shift laws at literal `k` is a natural rider and its own decision ([[decreases-word-measures-by-hand]] is where it reads words).

## Done when

The laws are theorems in `bitvec_nat.hthr` (or a `bitvec_shift_nat.hthr` beside it if the imports ask), with probes in `lib/_tests/std/bitvec` at a literal and a neutral width, a neutral and a literal shift, and a negative control (`k > n` where a law needs the bound).

## Log

- 2026-11-12: Merged to master as #588: the laws are in `lib/std/bitvec/bitvec_shift_nat.hthr` (`toNat_shift_left`, `toNat_shift_right`, `BitVec::low_mask` with `toNat_band_low_mask`, `toNat_band_complement_low_mask`, and the split `shift_right_shift_left_bor_low_mask`). The layout's run-time functions (`docs/layout-design.md` §4) are their first customer.
