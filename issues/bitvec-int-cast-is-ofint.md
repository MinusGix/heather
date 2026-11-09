---
title: BitVec::int_cast and BitVec::ofInt are one map, stated
status: closed
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

## Done (2026-11-09)

One definition, `BitVec::ofInt` in `bitvec.hthr`, in the ring's spelling (a
negative `-(k + 1)` is `ofNat(k + 1).neg()`). That spelling is the one `ring`
needs: a coefficient it writes must read back as the goal's `-k` by
conversion at an open width, where the complement spelling is stuck.
`BitVec::int_cast` is gone (`CommRingOfInt`'s `of_int := BitVec::ofInt`) and
`bitvec_div`'s definition with it; `SInt::ofInt` is unchanged and so reads the
same word. Renamed with it: `int_cast_eq` → `int_cast_ofInt` (`Ring::int_cast`
is `ofInt`), `int_cast_add`/`_mul` → `ofInt_add`/`ofInt_mul`, as `ofNat_*`
and `Rat::ofInt_*` are named.

The complement reading is now theorems:

- `BitVec::complement_toNat_add` (`bitvec_signed`): `!x` and `x` fill every
  bit, `(!x).toNat() + (x.toNat() + 1) = 2^n`.
- `BitVec::eq_neg_of_add` (`bitvec_ring`): inverses are unique.
- `BitVec::complement_eq_neg`: `x.complement() = (x + 1).neg()`, so `ring`
  reads `!x` once it is rewritten.
- `BitVec::ofInt_negSucc`: `ofInt(NegSucc(k)) = ofNat(k).complement()`.

`bitvec_ring` now imports `bitvec_signed` for the first. Probes in
`lib/_tests/std/bitvec/bitvec_ring_tests.hthr` (open width through `ring`,
literal width by `refl`).
