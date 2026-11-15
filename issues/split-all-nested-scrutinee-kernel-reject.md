---
title: split_all builds a term the kernel rejects at a match nested in a scrutinee
status: closed
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

## Log

- 2026-10-25: closed. Neither suspect: the motive and the `refl` leaf were
  both faithful. `refl` is not checked by the elaborator at all (it is a
  note for the gate), and the split handed it a false goal. The split on
  `c0` substituted `False`, which left the closed comparison
  `unsigned_lt_bit(64, 0, 0)` as the next match's scrutinee; the search split
  it like an open one, and its `True` case, which no run reaches, became the
  leaf goal `1 = 0`. The open-word form (`k(c, x, y) = h(c, x, y)` with
  `h` matching on `eq_bit(match c { False => x, True => y }, 1)`) was a
  second defect: the comparison was preferred to the match inside its
  operand, against the search's documented order, and once `c` was decided
  the other side's `eq_bit(match False { … }, 1)` was not recognised as the
  split `eq_bit(x, 1)`, so a leaf got `0 = h(False, x, y)`.
  Fixed in `crates/elab/src/goal_combinators.rs`: a case whose equation
  computation refutes is closed by `absurd` before anything else; the search
  takes a deeper blocker before a comparison, and reads a decided match in a
  comparison's operand as the arm it selects. The guarantee that the class
  does not recur is the splitter checking its own output: each split's
  motive at its scrutinee and each simplified goal must convert to the goal
  it stands for, and a `refl` leaf is converted where it stands, refused
  with its goal and case equations (docs/tactics/goal-combinators.md). Probes:
  `crates/elab/tests/bv_omega.rs`, `splits_comparisons_a_split_decides`.
