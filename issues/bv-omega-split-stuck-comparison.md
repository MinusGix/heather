---
title: Split a match stuck on a word comparison, for bv_omega's branches
status: closed
labels: [proofs,bitvec,metaprogramming]
created: 2026-09-26
updated: 2026-09-28
---

`decimal_line`'s `place` is a `match` on `s.unsigned_lt_bit(threshold)`. With
`bv_omega`, `place_step` still selects each branch by hand: a `match` on the
outcome, `leb_yes`/`leb_no`, a `j` to rewrite the match, and a `cong` under
`toNat`. A goal producer in the `split_all` family could split a match stuck
on a word comparison. It would hand each branch the comparison as a Nat fact
and leave the branch's word arithmetic to `bv_omega`.

The user's verdict of 2026-09-26 put this outside `bv_omega`'s first slice
(see [[bitvec-nat-lifting-tactic]]'s log).

## What it assumes from elsewhere

- **[[tactic-composition-ergonomics]]** owns how goal producers compose.
  Assumed here: that a split can be followed by a leaf at every branch, as
  `split_all; all_goals { … }` is.
- **[[bv-omega-bytes-and-comparisons]]** owns reading `unsigned_lt_bit` as a
  Nat order.

## Log

- 2026-09-28: Implemented in `split_all`: after finite locals, a bounded search exposes matches blocked on `unsigned_lt_bit` in the goal, including below `toNat`. Each split uses an ordinary convoy with a motive abstracting the exposed match, computes the constructor cases in its branch goals, and repeats the search before checking the leaf. The branch retains its Boolean equation and, when the bridge library is available, a Nat order fact usable by `omega` as well as `bv_omega`.

  Restoring steps also needed the Nat value of an `ofNat`/`word_of_nat` comparison operand before a subtraction's no-borrow check. `bv_omega` now supplies that value only after independently checking its fit bound; a wrapping operand contributes no such value equation.

  Regression coverage in `crates/elab/tests/bv_omega.rs`: kept and taken restoring steps, both live branches, an open threshold, open widths, nested matches and nested word arguments, finite locals, a generated-name collision, word equality, `omega` and `refl` leaves, and refusals for a false branch and an overflowing branch. The existing finite-local combinator tests remain unchanged. The user’s pre-existing `decimal_line` and check-cost edits are outside this change.
- 2026-09-28: Validation: full `scripts/test` passed (3,033 passed, 0 failed, 5 ignored), including the new comparison-split regressions and the unchanged goal-combinator tests. `scripts/issue check` and `git diff --check` passed. The full suite ran outside the sandbox after its initial attempt was stopped by an EPERM launch restriction.
