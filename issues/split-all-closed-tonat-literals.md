---
title: split_all's comparison facts leave closed toNat(ofNat(k)) as omega atoms
status: open
labels: [proofs,tactics,bitvec]
created: 2026-10-02
updated: 2026-10-02
---

`split_all` gives each comparison it splits a Nat fact for `omega`, but the
fact spells the constant as an atom: `Le(toNat(ofNat(14)), toNat(byte))`.
Plain `omega` takes `toNat(ofNat(14))` as an unknown, so it cannot close a
case that is impossible between two comparisons. For example, wc's step at
`byte ≥ 14` and `byte < 11`. Probe 2026-10-02:
`wc_step(s, byte).lines = s.lines + bit(newline_byte(byte))` by
`split_all; all_goals { omega }` gets stuck with exactly those atoms, while
`bv_omega` closes it.

Fix: when the width is a literal and `k < 2^w`, `split_all` states the fact
at the literal (`14 <= toNat(byte)`), or `omega` reads a closed
`toNat(ofNat(k))` as `k`. Small. `bv_omega` is the workaround, and arguably
the right leaf for byte steps anyway.
