---
title: "Z/n as a commutative ring at every modulus, a field at a prime, words as the instance at 2^w"
status: open
labels: [stdlib,mathematics,number-theory,algebra]
area: mathematics
milestone: [math-number-theory,hih-crypto]
blocked-by: [nat-gcd-and-modular-arithmetic]
created: 2026-11-10
updated: 2026-11-10
---

Area 4 of the 2026-11-10 ranking.

`lib/std/bitvec/bitvec_ring.hthr` made words a ring at `2^w`
(`machine-words-modular-ring`, closed 2026-11-09). There is no ring at
any other modulus, which is where cryptography after SHA-2 lives
(Poly1305 in Z/(2^130 − 5), Curve25519 in Z/(2^255 − 19)) and where a
compiler's division by a constant is proved.

## Scope

- `ZMod(n)` for `0 < n`, as a canonical representative below `n` so
  equality is `=` and closed facts evaluate; `CommRing` instance; the
  ring homomorphism from `Int`, with `ModEq` as its kernel.
- At a prime, the inverse from [[nat-gcd-and-modular-arithmetic]] and a
  `Field` instance for the `ring`/field tactics; Fermat and Euler.
- The isomorphism with `BitVec(w)` at `n = 2^w`, so word theorems and
  `ZMod` theorems transfer.
- `ring` accepts `ZMod(n)` goals (it reads class operations through
  dictionaries already).
- Multiplicative-inverse division: for odd `d`, exact division by `d` on
  words is multiplication by its inverse mod `2^w`, as the first
  compiler client ([[function-ir-pass-arithmetic-folds]]).

## Done when

One limb-free specification of Poly1305's field arithmetic is stated
over `ZMod`, and the exact-division fold is a theorem over words.

## What it assumes from elsewhere

- **[[nat-gcd-and-modular-arithmetic]]** owns gcd and inverses.
