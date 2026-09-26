---
title: Split a match stuck on a word comparison, for bv_omega's branches
status: open
labels: [proofs,bitvec,metaprogramming]
created: 2026-09-26
updated: 2026-09-26
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
