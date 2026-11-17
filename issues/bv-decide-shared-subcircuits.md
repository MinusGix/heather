---
title: bv_decide: share equal subcircuits in the bit-blaster
status: open
labels: [bitvec,solver,tactics,perf]
area: tactics
created: 2026-11-17
updated: 2026-11-17
---

`Circ::and` (`lib/std/tactic/bitblast.hthr`) builds a new gate every time it is asked, so two spellings of one word (`x + y`, `y + x`; the program's mask-and-shift and the decoder's `concat`) blast to two different circuits and the solver must prove them equal. Hash-cons the and-gates, with each gate's two inputs in a fixed order, so a gate asked for again is the one already built: `x + y = y + x` is then one literal compared with itself, with no proof steps, and an equivalence keeps only the part that really differs.

The growth invariant `Circ::Makes` still holds: a gate found again computes the same `and` in every circuit grown from the one that built it. The lookup table is part of the circuit (a `NatMap` keyed by the pair).

Parent: [[lrat-certified-bitvector-decision]]. Design: `docs/tactics/bv-decide-design.md`.

## Log

- 2026-11-17: built gate-level hash-consing and set it aside (branch `bv-gate-table-experiment`, commits 5c2aaf4b and 8b642a4f). `Circ` carried a table from the ordered pair of input codes to the node, `Circ::Good` its invariant (`Circ::Shares`: every entry is a node of the circuit that is the and of its two inputs at every input), and `Circ::and` looked up before building; the proofs went through and 8-bit `x + y = y + x` needed 2 hints instead of 1497. But the kernel pays for every lookup and insertion while it builds the circuit inside a conversion: a 64-bit adder's circuit went from about 180k to 2.4M kernel steps (a nested `NatMap`; a `NatMap` keyed by the larger input with list rows was no better), past one conversion's budget, so every 64-bit claim failed. A `NatMap` update is several hundred kernel steps, about ten times a `push`.
  Most of what sharing bought now comes from [[bv-decide-normalize]]: commuted and reassociated spellings normalize to one expression before blasting. What is left is sharing a subexpression that occurs twice inside a claim the normalizer does not close (`x * y + x * y = (x * y) << 1` blasts the multiplier twice). Routes: a memo of blasted word subexpressions keyed by structural equality (a few entries per claim, so a list scan; the entry invariant is `Circ::MakesWord`'s), or the gate table built once in a staged obligation (the circuit as a literal) so that pieces do not rebuild it.
- 2026-11-17: A trie level now reads the key's low bit as `Nat::low_bit` defined two at a time like `half` (lib/std/num/nat.hthr, `low_bit_sub` keeps the old reading as a theorem), which the kernel runs on numerals in a few steps: a 30-bit key's set and get went from about 3000 kernel steps to about 2100, and bv_decide's proof checks lost a tenth to a third. Still several hundred steps per lookup, so the gate table stays set aside.
