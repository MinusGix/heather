---
title: BitVec rotates, byte swap, widening multiply and add with carry, with cheap evaluation
status: open
labels: [bitvec,stdlib,mathematics,performance]
area: heather-in-heather
milestone: [crypto-hash]
created: 2026-11-10
updated: 2026-11-10
---

`lib/std/bitvec` has shifts, extensions, `concat`, `split` and the ring
ℤ/2ⁿ, but no rotate, no byte swap, no widening multiply, no add with
carry, no population count and no leading-zero count. Hashes and ciphers
are written in exactly these, and so are bit sets and the decimal printer.

Measured for `docs/native-lexer-crypto-roadmap.md` (probes in the project
folder's `native-roadmap/`, release binary, cloud box, width one):

| probe | kernel steps |
|---|---|
| a 32-bit rotate by 13 as `shift_right(13) | shift_left(19)` | 2,981 |
| the same rotate as `drop_low(13, 19).concat(take_low(13, 19))` | 684 |
| one 32-bit `add` | 1,388 |
| SHA-256's Σ0 (three rotates from shifts) | 7,618 |
| one SHA-256 round | about 21,000 |
| sixteen rounds | 338,559 |
| one block by a single `refl` | `OutOfFuel` at 2^20 |

A shift by `k` is `k` one-bit shifts, each linear in the width, so a rotate
built from shifts pays for the count twice.

## Scope

- `BitVec::rotl`/`rotr` defined by `split` and `concat` (linear in the
  width, independent of the count), with: the shift-pair spelling as a
  theorem, inverses, composition (`rotr(a).rotr(b) = rotr((a + b) mod n)`),
  distribution over the bitwise operations, and the `toNat` reading.
- `bswap` over `bytes_le`/`bytes_be`; `mul_wide` (`BitVec(n) → BitVec(n) →
  BitVec(n + n)`, with `toNat` the product); `adc`/`sbb` returning the
  carry, tied to `carry_add`; `popcount`, `clz`, `ctz`.
- Each with a definition cheap under kernel evaluation, since
  specifications are checked by evaluating them.
- Surface symbols are a separate question (`integer-operator-symbols`
  already took `<<` and `>>`); method names suffice here.

## Done when

SHA-256's "abc" block is one `refl` (or two stage theorems), and `ring`
and the bit-vector automation still read goals that mention the new
operations through their unfolding lemmas.

## What it assumes from elsewhere

- **[[sha2-specification]]** is the first client.
- **[[lrat-certified-bitvector-decision]]** owns deciding bit-vector
  identities. Assumed here: nothing; the laws above are proved by hand or
  by induction on the width.
