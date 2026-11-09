---
title: Machine words as ℤ/2ⁿ: congruence mod m and a ring instance
status: closed
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

## Resolution (2026-11-09)

Landed in three layers, each in its type's file.

- **`nat.hthr`**: the congruence kit. `add_mul_mod` (a multiple of the
  divisor changes no remainder) and everything read off it: `mod_mod`,
  `mod_self`, `mul_mod_self`, `mod_add_mod`/`add_mod_mod`/`add_mod`,
  `mul_mod_left`/`mul_mod_right`/`mul_mod` (the existing `mod_mul_mod` is the
  divisor-multiple law, hence the names), `pow_mod`, `mod_mod_of_dvd` (no
  positivity on the outer divisor) and the power facts `pow_dvd_pow_add`,
  `mod_pow_mod`. `Nat::ModEq(m, a, b)` is equality of remainders, with
  `modeq_refl/symm/trans/mod/add/mul/pow/add_mul`.
- **`int.hthr`**: `Int::ModEq(m, a, b)` = `∃ k, a = b + k·m`, with
  `modeq_refl/symm/trans/add/mul_l/mul` and `modeq_ofNat` from `Nat::ModEq`.
- **`bitvec_nat.hthr`** (its header now names a modular half and a
  no-overflow half): `toNat_ofNat_mod` (`ofNat` keeps the low `n` digits, at
  every width) is the root; then `ofNat_mod`, `ofNat_modeq`, `toNat_inj`;
  every operation as `ofNat` of the Nat one (`add_eq_ofNat`, `sub_eq_ofNat`
  = `a + 2^n - b`, `neg_eq_ofNat`); the values `toNat_add_mod` (P6),
  `toNat_mul_mod`, `toNat_sub_mod`, `toNat_neg_mod`; `ofNat` a homomorphism
  at every width, `ofNat_add` (P3), `ofNat_mul`, `ofNat_pow` (new
  `BitVec::pow`, designated `^`), and `ofNat_sub` under `y <= x`; truncation
  `truncate_ofNat`, `truncate_add`, `truncate_mul` (and `truncate_neg` in
  `bitvec_ring`); the signed reading `toInt_modeq`. `add_ofNat_sum` lost its
  bound's use and `toNat_add` is `toNat_add_mod` with `mod_of_lt`; their
  signatures are unchanged.
- **`bitvec_ring.hthr`** (new): the ring laws (`add_assoc`, `add_neg`,
  `mul_assoc`, `mul_comm`, distributivity, units) and
  `CommRing`/`CommRingOfInt<BitVec(n)>` at `RelId`, with `≈` designated
  `RelId`. The integers' image is `BitVec::ofInt` (numerals and negated
  numerals; it was `BitVec::int_cast` until [[bitvec-int-cast-is-ofint]]), proved equal to `Ring::int_cast` so its laws are the generic
  ones.
- **`ring`** (`crates/elab/src/ring.rs`): an `=` goal at a carrier whose `≈`
  is `RelId` and which has `CommRingOfInt` is read as the `≈` goal it
  unfolds to (`identity_equation`), so `ring` proves `a * b + a = a * (b +
  1)` at `BitVec(32)` as written; and a carrier numeral spelled
  `T::ofNat(2, n := n)` is a constant candidate (`of_nat_numeral`),
  confirmed by conversion as before.

Probes: `lib/_tests/std/bitvec/bitvec_ring_tests.hthr` (P1 at `BitVec(64)`
and open widths, numerals, a hypothesis, P3, P6, wrap-around, truncation, the
signed reading, and the refusal at characteristic 2: `a + a ≈ 0` at
`BitVec(1)` holds but is no commutative-ring identity).

Done-when: `ring` proves a word identity at `BitVec(64)` (yes) and P6 is a
library lemma (`BitVec::toNat_add_mod`). The `Add` fold citing `ofNat_add` is
[[function-ir-pass-arithmetic-folds]]'s to write; the lemma it waits on is
here, with `ofNat_sub` for its `Sub` case.

Left: `ring` could not read `-` at words, because `BitVec::sub` is its own
ripple and not `a + -b` by definition (since read through a `SubtractionLaw`
instance, [[ring-carrier-subtraction-law]]). `BitVec::int_cast` and
`bitvec_div`'s `BitVec::ofInt` were one map spelled two ways, now one
definition ([[bitvec-int-cast-is-ofint]]). The ~240 `fits` premises in native, arch
and os are unchanged; each can now be dropped where its lemma only needed the
modular statement, as callers are next touched.
