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
