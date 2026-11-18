---
title: bv_decide: goals as people write them
status: open
labels: [bitvec,solver,tactics,feature]
area: tactics
created: 2026-11-17
updated: 2026-11-17
---

Accept `x < y` and `x ≤ y` at `Prop`, `x ≠ y`, and `a.toNat() = b.toNat()` / `a.toNat() = n` (through `toNat_zero_extend`, as `examples/utf8/utf8_check.hthr`'s code words do by hand). Treat atoms that are not locals (a field, a call the reader cannot unfold) as fresh words, abstracted like locals, instead of refusing them.

Parent: [[lrat-certified-bitvector-decision]].

## Log

- 2026-11-17: `x < y`, `x <= y` (`unsigned_lt`/`unsigned_le` at `Prop`) and `x ≠ y` are read as goals and hypotheses (`BVClaim` in lib/std/tactic/bv_decide.hthr). The tactic view now shows a type held as a term (`¬(a = b)`'s argument) as the equation or function type it decodes to, which `≠` needed. Left: `toNat` equations, non-local atoms as fresh words.
