---
title: Migrate Rat to Pos<Nat> sugar and delete the shifted Pos
status: closed
labels: [stdlib,mathematics]
created: 2026-10-10
updated: 2026-10-14
---

Once [[pos-binder-sugar]] has record fields, migrate `Rat` to
`{ num: Int, den: Pos<Nat> }` and the cancellation lemmas
(`Int::mul_cancel_pos_r`, `Int::mul_le_cancel_pos_r`) to `p: Pos<Int>`, then
delete `lib/std/pos.hthr`'s `Pos { pred }`. Most of `pos.hthr` (`mul_val`,
`mul_int`, the restated omega goals) should go away rather than be ported.

Watch: representation equality of two `Rat`s now compares proofs. `Nat::Le`
proofs are unique (it computes to `True`/`False` on constructors), but the
lemma is not in `lib/` yet.

## What it assumes from elsewhere

- **[[positive-naturals-and-rationals]]** landed the code being migrated.

## Log

- 2026-10-10: Filed from [[positivity-evidence]].
- 2026-10-13: 2026-10-13: Unblocked: [[pos-binder-sugar]] landed record fields (`den: Pos<Nat>`, rule `Rat::den_positive`; note §11). A record with parameters cannot take one yet ([[pos-sugar-unsupported-positions]]); `Rat` has none.
- 2026-10-14: LANDED (docs/positivity-evidence-design.md §14). lib/std/pos.hthr deleted. Rat is { num: Int, den: Pos<Nat> }, read into Int as x.den.int() (Nat::int, in rat.hthr); literals are honest (Rat(OfNat(1), 2) is ½). The Pos::mul bridges went; Rat::den_add/den_mul (refl) replace them for ring, and Nat's own laws for same_of_parts. The cancellation lemmas moved into rat.hthr with p: Pos<Int>; the two Rat calls name p_pos := y.den_pos, since no rule lifts 0 < n to 0 < OfNat(n) (the rule-size check refuses it). Found on the way and fixed: a record with a Pos field has a dependent spine, so its fields are named projections, which ring and omega did not read through (Elaborator::named_field_read). Representation equality now compares den_pos proofs; nothing in lib/ needs the Nat::Le uniqueness lemma, so it is not written.
