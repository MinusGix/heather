---
title: Machine words as ℤ/2ⁿ: congruence mod m and a ring instance
status: open
labels: [bitvec,native,algebra]
area: mathematics
milestone: [nh-front,hih-passes]
created: 2026-11-09
updated: 2026-11-09
---

`lib/std/bitvec/bitvec_nat.hthr` states word/Nat facts with no-overflow
premises only ("Bounds are mathematical, never modular"), and the modular
half was never added: `nat.hthr` has no `add_mod`/`mul_mod`/`mod_add_mod`
and no congruence relation, `BitVec` has no ring instance, so `ring` refuses
word goals (probe P1), `ofNat(a) + ofNat(c) = ofNat(a + c)` at an open width
has no lemma (P3), and `omega` cannot link `toNat(a + b)` to `(toNat a +
toNat b) mod 2^n` (P6). About 240 `Nat::pow(2, …)` side conditions in native,
arch and os are `fits` premises threaded to the no-overflow lemmas.
`docs/native-mathematics-survey.md` §2; survey rank 2.

## Scope

- Congruence modulo `m` on `Nat` and `Int` (`ModEq`): an equivalence
  compatible with `+`, `*` and powers; `add_mod`, `mul_mod`, `mod_add_mod`,
  `mod_mod_of_dvd`, and the power-of-two facts. In `nat.hthr`/`int.hthr`.
- `BitVec(n)` as ℤ/2ⁿ: `toNat` of `add`, `mul`, `neg`, `sub` modulo `2^n`;
  associativity and distributivity; a ring instance so `ring` normalises
  word expressions.
- `ofNat` a semiring homomorphism at every width (`ofNat_add`, `ofNat_mul`,
  `ofNat_pow`), truncation a ring homomorphism; `toInt(a) ≡ toNat(a) (mod 2^n)`.
- The existing no-overflow lemmas stay, restated as corollaries where that
  shortens them.

## Done when

`ring` proves a word identity at `BitVec(64)`, the `Add` fold of
[[function-ir-pass-arithmetic-folds]] cites `ofNat_add` at an open width,
and P6 is a library lemma.

## What it assumes from elsewhere

- **[[function-ir-pass-arithmetic-folds]]** owns the folds. Assumed here:
  only that it needs `ofNat` laws at every width.
- **[[bitvec-division-laws]]** owns division; untouched.
