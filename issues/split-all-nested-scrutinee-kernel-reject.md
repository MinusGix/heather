---
title: split_all builds a term the kernel rejects at a match nested in a scrutinee
status: open
labels: [tactics,elaboration,soundness-gap]
area: tactics
created: 2026-10-25
updated: 2026-10-25
---

Found while writing the loop certificates of
[[function-ir-verified-loop-planning]]. The elaborator accepts the proof and
the kernel refuses it (`NotConvertible`), so nothing unsound is admitted,
but `split_all` reports success on a goal it did not prove.

```
fn f(c0: Bool) → Nat {
    match (match c0 { False => @bitvec::BitVec::unsigned_lt_bit(64, @bitvec::BitVec::ofNat(64, 0), @bitvec::BitVec::ofNat(64, 0)),
                      True => @bitvec::BitVec::eq_bit(64, @bitvec::BitVec::ofNat(64, 0), @bitvec::BitVec::ofNat(64, 0)) }) {
        False => 0,
        True => 1,
    }
}
fn g(c0: Bool) → Nat { match c0 { False => 0, True => 1 } }

theorem f_g(c0: Bool): f(c0) = g(c0) { split_all; all_goals { refl } }
// error: the kernel rejected `f_g`: NotConvertible … `1` and `0` are not
```

`f(False) = 0` and `f(True) = 1` are both `refl`, and an explicit
`match c0 as λ b => f(b) = g(b) { False => refl, True => refl }` checks.
With `False`/`True` literals in place of the comparisons
(`match (match c0 { False => False, True => True })`) `split_all` is fine,
so the literal comparisons computing under the split are involved. The
same happened with `eq_bit(64, match c { … }, ofNat(1))` as a match's
scrutinee over open words.

Suspects: `cases_request`'s motive (`goal_combinators::co_occurrences`
abstracts positions that reach the scrutinee through a definition), or the
elaborator's `refl` leaf accepting a conversion the kernel does not. Either
way the elaborator and the kernel disagree, which is the defect: find which
check is lenient. The loop certificates write their case splits as explicit
`match … as` convoys instead, so nothing waits on this.
