---
title: Numerals at Rat, and algebra_rel's Semigroup clashing with algebra's
status: open
labels: [stdlib,notation,traits,ergonomics]
created: 2026-10-15
updated: 2026-10-15
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
