---
title: BitVec::int_cast and BitVec::ofInt are one map, stated
status: open
labels: [bitvec,algebra]
area: mathematics
milestone: [none]
created: 2026-11-09
updated: 2026-11-09
---

Two maps from `Int` to `BitVec(n)` exist: `bitvec_div`'s `BitVec::ofInt`
(a negative `-(k + 1)` is `ofNat(k).complement()`, no subtraction from `2^n`)
and `bitvec_ring`'s `BitVec::int_cast` (a negative is `ofNat(k + 1).neg()`),
which is the `of_int` of the word ring because its laws come from
`Ring::int_cast`'s (`BitVec::int_cast_eq`). They are the same function; the
missing fact is `x.complement() = x.neg().sub(1)` (or its `toNat` form,
`2^n - 1 - x.toNat()`), after which one can be defined as the other or the
equation stated, so a signed constant written either way reads the same
under `ring`.

## What it assumes from elsewhere

- **[[machine-words-modular-ring]]** owns `BitVec::int_cast`. Assumed here:
  only that it is the ring's `of_int`.
