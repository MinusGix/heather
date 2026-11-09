---
title: Lemma registries that tactics read, so a new type gets automation without editing a tactic
status: open
labels: [tactics,design,ergonomics]
area: tactics
milestone: [lang-proof-modularity]
created: 2026-10-31
updated: 2026-11-08
---

Round P3 of `docs/compiler-milestones-proposal.md` (§6.2, §7): lemma registries that automation reads, so a
new type gets automation by registering lemmas rather than by editing a
tactic.

## Scope

- One declaration-side registration mechanism, as [[proof-modularity-design]] decides it.
- `mono` reads it in place of its hard-coded carrier table (`mono_carriers`, `lib/std/tactic/mono.hthr`). `norm_num` reads it for its carriers.
- Say what [[mono-class-laws]] and [[monotonicity-tactic]] still own afterwards.

## Done when

A new ordered carrier gets `mono` and `norm_num` by registering its lemmas, with no edit to either tactic, and `mono_carriers` is gone.

## Log

- 2026-11-08: 2026-11-08: [[simp-tactic]] wants the same registration for its default lemma set, so this mechanism should not be shaped only around mono and norm_num.
