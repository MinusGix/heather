---
title: SHA-2 as a specification: one definition generic in the word width, with the standard's vectors
status: open
labels: [cryptography,stdlib,proofs]
area: heather-in-heather
milestone: [crypto-hash]
created: 2026-11-10
updated: 2026-11-10
---

Stage C0 of `docs/native-lexer-crypto-roadmap.md` §4: SHA-2 as a pure
Heather function, the specification every later stage is proved against.

## Scope

- `lib/std/crypto/sha2.hthr`: the construction once, generic in the word
  width (32 or 64) and a parameter record (rotation counts, round
  constants, initial values, block and length sizes), in FIPS 180-4's
  shape: padding, the message schedule as a list, the round, the
  compression function, the fold over blocks. SHA-224, 256, 384 and 512
  (and 512/256) are its instances.
- Known answers by evaluation: the short NIST vectors as `refl` theorems,
  in stages where one block is past a declaration's fuel
  (`docs/proof-patterns.md`, stage theorems). Longer vectors wait for the
  native run ([[sha2-compress-native]]).
- An importer: a Rust test that turns NIST response files into such
  theorems, as the per-line lexer gate does ([[heather-lexer-evaluated]]).
- The streaming theorem, for any block function: `update(update(s, a), b)
  = update(s, a ++ b)`, and `finish` as padding then `update`. Proved over
  an abstract compression function, so BLAKE2 and later constructions
  reuse it.
- A low-level functional form (a rolling sixteen-word window, the state as
  eight words) proved equal to the list specification: the function
  [[sha2-compress-native]] marks `runtime fn`.

## Done when

`sha256(bytes)` and `sha512(bytes)` check NIST's short vectors by
evaluation, the streaming theorem is proved for an abstract block function,
and a negative control holds (one wrong round constant refuses a vector).

## What it assumes from elsewhere

- **[[bitvec-rotates-and-wide-ops]]** owns rotates. Assumed here: that a
  rotate evaluates in time linear in the width.
- **[[loop-invariant-rules]]** would shorten the rolling-window proof; it
  is not a blocker.
