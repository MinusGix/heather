---
title: Numerals at Rat, and algebra_rel's Semigroup clashing with algebra's
status: closed
labels: [stdlib,notation,traits,ergonomics]
created: 2026-10-15
updated: 2026-10-20
---

`lib/std/rat.hthr` spells every constant as a call: `Rat::zero()`,
`Rat::one()`, `Rat::ofInt(OfNat(n))`, and at `Int` it writes `OfNat(1)` where
`1` should do. Found in the rat style review on PR #42 (2026-10-15).

Two pieces:

- **`Numeral<Rat>`**: an instance with `ofNat := λ n => Rat::ofInt(OfNat(n))`
  would let the laws read `0 <= x`, `x * 1 ≈ x`.
- **The `Semigroup` name clash**: numerals at `Int` need `import algebra`
  (where `Numeral` and `Int`'s instance live), and importing `algebra` beside
  `algebra_rel` makes `Semigroup` ambiguous. `algebra::Semigroup` is the
  operation-only class; `algebra_rel::Semigroup` is the class modulo a
  relation. They should not share a name. Renaming the relational one (for
  example `SemigroupRel`) unblocks numerals in every setoid client, not only
  `Rat`. Today the workaround is a list import, `import algebra_rel::{Semigroup}`
  (docs/modules-design.md §3).

## Acceptance

- `algebra_rel`'s classes no longer collide with `algebra`'s; a module can
  import both without a list import.
- `Rat` has a `Numeral<Rat>` instance and its public statements use numerals
  where they read better than the constructor calls.

## Log

- 2026-10-20: Done. `algebra_rel::Semigroup` is now `SemigroupRel` (Mergeable, OrderedAddGroup, Rat, CReal and the positive-subtype showcase follow); rat, creal and ordered_field import `algebra_rel` whole. `Numeral<Rat>` already existed (PR #63); this round made numerals the only spelling of a constant: `Rat::zero()`/`Rat::one()` and `CReal::zero()`/`CReal::one()` are deleted, `Numeral<CReal>` added (`CReal::ofRat(Rat::ofInt(OfNat(n)))`), and rat and creal `export algebra::{Numeral}` so a client writes `0` without importing `algebra`. Two spellings were not an option: evidence-rule prefilters and `rel_cong` compare heads, so `x.Apart(Rat::zero())` missed rules stated at `x.Apart(0)`, and `CReal::ofRat_apart`'s premise `q.Apart(0)` is larger than a conclusion mentioning `CReal::zero()` (the Paterson check refused it). Residue: all-numeral relations default to Nat silently, [[all-numeral-relations-default-to-nat]].
