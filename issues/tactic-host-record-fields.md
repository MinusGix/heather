---
title: Let tactics read record fields, apply generic class lemmas, and solve holes through their types
status: open
labels: [tactics,host]
area: tactics
created: 2026-10-30
updated: 2026-10-30
---

Three gaps the cast slice (docs/casting-design.md §9) worked around in the
tactic host (`crates/elab/src/host.rs`):

- **No field access from the tactic side.** A record value, or a record
  type, views as `HOther`, and records have no projection globals, so a
  tactic cannot read `f.map_add` off a morphism it holds. `cast.hthr` reads
  the laws through one theorem per field (`OrderedRingHom::add_law`, …),
  which is a wrapper per field for every record a tactic wants to read.
  Wanted: an `Expr` form for a projection (or a view of a record value's
  fields), so a tactic can apply a field directly.
- **`apply` of a generic class lemma at a concrete carrier.** Applying
  `StrictOrder::…` (a lemma under a class section) to a `Rat` goal fails
  with `?1 -> ?1 -> Type where same expected`: the relation's carrier is not
  inferred from the goal. `mono`'s cast step uses per-carrier copies
  (`Rat::le_of_same_r`, `CReal::lt_of_same_l`, …) instead.
- **A hole's declared type is not unified with its solution's.** Solving a
  hole by unification does not compare the solution's type with the hole's,
  so a hole that occurs only in other holes' types (a structural record's
  type parameter) stays unsolved; `cast.hthr` solves it by hand
  (`cast_targeted`).
