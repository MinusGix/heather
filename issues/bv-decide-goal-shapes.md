---
title: bv_decide: goals as people write them
status: open
labels: [bitvec,solver,tactics,feature]
area: tactics
created: 2026-11-17
updated: 2026-11-18
---

Accept `x < y` and `x ≤ y` at `Prop`, `x ≠ y`, and `a.toNat() = b.toNat()` / `a.toNat() = n` (through `toNat_zero_extend`, as `examples/utf8/utf8_check.hthr`'s code words do by hand). Treat atoms that are not locals (a field, a call the reader cannot unfold) as fresh words, abstracted like locals, instead of refusing them.

Parent: [[lrat-certified-bitvector-decision]].

## Log

- 2026-11-17: `x < y`, `x <= y` (`unsigned_lt`/`unsigned_le` at `Prop`) and `x ≠ y` are read as goals and hypotheses (`BVClaim` in lib/std/tactic/bv_decide.hthr). The tactic view now shows a type held as a term (`¬(a = b)`'s argument) as the equation or function type it decodes to, which `≠` needed. Left: `toNat` equations, non-local atoms as fresh words.
- 2026-11-18: `toNat` comparisons (`<`, `<=`, `=`, `≠`, at `Prop` and as `Nat::leb`/`Nat::same`), their negations in both spellings (`¬(a < b)` and the `a < b → False` an `induct` arm's refuted test reads as), and a word chosen by an `if` (the goal split on its test, each case decided) are read: `examples/utf8/utf8_check.hthr` relates the decoder to the program with no lemma restating either. Left: non-local atoms as fresh words; a Boolean call on both sides (`is_utf8(r)`) is the case the UTF-8 proof still rewrites away by hand.
- 2026-11-18: statements joined by `∧ ∨ ↔ ¬` and `False`, as goals and hypotheses, nested to any depth (`BVStmt`, `BVCx::bridge`, the `layout_and`/`or`/`not`/`iff_p`/`false` lemmas in bitblast.hthr): a loop condition written as one Prop reads in both arms (issues/utf8-example-elegance.md item 4). Left: non-local atoms as fresh words.
- 2026-11-18: an equation on a word chosen by an `if` reads as `(c ∧ a = k) ∨ (¬c ∧ b = k)` without splitting (`SIte`, `layout_ite_p` and `_hyp`): the host's `Abstract` takes any term and `Unfold` reduces a β/ι head. Unicode's byte table over four `u8`s decides in seconds (`table_*` probes). Over 64-bit words widened from bytes the clause list is past one conversion (docs/tactics/bv-decide-design.md, Open). Left: non-local atoms as fresh words.
- 2026-11-18: a word call taking an argument the bit-blaster cannot model (a list) is an atom, the same call twice one atom (by conversion); an equation on such a call is read through its tests first. Left: Boolean calls as atoms.
