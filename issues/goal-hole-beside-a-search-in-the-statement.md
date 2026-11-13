---
title: A goal hole in a body whose statement names a search is an internal error
status: closed
labels: [elaboration,goals,diagnostics]
area: language
created: 2026-11-13
updated: 2026-11-13
---

```heather
fn word_below(i: BitVec(64), inside: i.toNat() < 64 := bv_omega) → BitVec(64) { i }

fn climb(acc, j: BitVec(64)) → BitVec(64)
    decreases (48 - j).toNat() {
    if h: j < 48 { climb(acc + word_below(j + 16), j + 1) } else { acc }
}

theorem climb_step(acc, j: BitVec(64), h: j < 48): climb(acc, j) = climb(acc + word_below(j + 16, inside := bv_omega), j + 1) {
    trans(climb_unfold(acc, j), ?)
}
// internal: more goals than the pre-count reserved
```

The statement gives a parameter's proof by a search (`inside := bv_omega`) and the body leaves a goal `?`. The report should be the goal with its statement; instead the goal arena runs out of the slots counted for the declaration. Seen 2026-11-13 while writing a probe for PR #607 (the probe was written another way); not reduced further, so the search in the statement may not be the needed part.

## Done when

The declaration above reports its open goal, with a probe in `lib/_tests`.

## Log

- 2026-11-13: Two causes, both fixed (branch claude/project-thread-m5i5zj).

  1. `count_tactic_slots` walked only the body, the `on`s and the value defaults, never the telescope or the result type, so a `bv_omega` written in the statement had no slot counted for it; its lifted proof took the slot counted for the body's `?`, and the `?` then ran out. Reduced form: `theorem t(j: BitVec(64), h: j < 48): word_below(j + 16, inside := bv_omega) = j + 16 { ? }` (the `decreases` function was not needed; two searches happened to work, because the second's `omega` atom list asks for a capacity restart that the first alone never does). The tactic count is now the hole count's walk with another score (`count_holes_impl::Tally`), so the two look at the same places by construction: types, the `decreases` measure and nested blocks' `on`s included.
  2. Once reported, the goal could not be discharged when its proof mentions the lifted slot through the statement (`on ?rest := refl` there): `solve_goals` strengthened the discharge out of the goal world with `0` for every slot, the lifted one included, and the kernel refused `0` as the proof of `toNat(j + 16) < 64`. Discharges are now kept in the goal world and re-scoped by `lift_proved` with the lifted slots as the constants it commits, like a lifted proof.

  Probes: `lib/_tests/std/tactic/bitvec_omega_tests.hthr`, "A search in a declaration's statement, beside a goal" (result type, parameter type, `omega`'s atom list, body and statement together, and the open goal as the negative control). Left: the reported statement spells the lifted proof as its slot (`inside := u3^{·; x1; x0}`), not as `bv_omega`.
