---
title: Migrate Rat to Pos<Nat> sugar and delete the shifted Pos
status: open
labels: [stdlib,mathematics]
created: 2026-10-10
updated: 2026-10-13
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
