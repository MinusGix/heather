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

- 2026-11-08: mechanism and `mono` done (docs/registered-values-design.md).
  `name_of(p)` is a checked qualified key; `register def x: T = e;` enters
  `x` in a registry under `T` (a module event: images, cutoff digest, slice
  replay); `registered(T)` lists the import closure's values, and as a
  parameter default it is read at the call, so `by mono()` sees its client's
  tables. `mono_carriers` and `mono_classes` are gone: each carrier
  registers `MonoEntry` values beside its lemmas (`mono_laws.hthr` holds the
  types, and `Nat`'s), `ordered_field` the classes', `big_operator` the
  sums'. A misspelled or renamed lemma is now an error at its table, where
  it used to be a law the tactic silently skipped. A string literal needs
  `string` only in the import closure. Left: `norm_num`'s carriers (its
  done-when half), `cast`'s edges and carriers, `interval`'s boxes and heads,
  and `grind_using`'s string lemma names, each the same move.
