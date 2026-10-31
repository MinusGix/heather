---
title: Cast reading through a morphism in scope, not only a registered edge
status: closed
labels: [tactics,casting,algebra]
area: tactics
created: 2026-10-31
updated: 2026-10-31
---

`mono` reads an image through a cast edge (`(a + c).rat() <= x + y` from
`a.rat() <= x`, `c.rat() <= y`, by `Dyadic::rat_hom`'s `map_add`), but the
edges it consults are the global names in `cast_edges()`
(`lib/std/tactic/cast.hthr`, `cast_hom_among`). Generic code takes its
morphism as a parameter ([[casting-standard]] §5.6:
`section<K: OrderedField(…)>({map: Rat → K}, hom: OrderedRingHom<Rat, K>(…))`),
and there `mono` cannot read `map(Dyadic::add(a, c).rat())`: the morphism is
a local, and nothing names it. Checked on 2026-10-31 (prototype for
[[interval-containment-once-over-ordered-field]]): `by mono_with([hx, hy])`
proves `map(a.rat()) + map(c.rat()) <= x + y` at the class carrier, and
fails on `map(Dyadic::add(a, c).rat()) <= x + y` with "nothing proves this
goal".

Wanted: a local (or section binder) whose type is `OrderedRingHom<A, B>(…)`
or `OrderedSemiringHom<A, B>(…)` counts as an edge for the goal it is in
scope of, the same way a registered one does; the composite through a
registered edge (`Dyadic::rat_hom` then `hom`) too, which is what the
interval statements need (`map(d.rat())`).

Without it, a generic containment proof is written with the laws named
(`hom.map_respects`, `hom.map_add`, `StrictOrder::le_respects` with six
points), where its `CReal` twin is two `by mono_with` lines. With it, the
generic section is the `CReal` file's proofs moved, and proving once is a
plain win.

## Resolution

- 2026-10-31: A local whose type is `OrderedRingHom<A, B>(…)` or
  `OrderedSemiringHom<A, B>(…)` is an edge (`cast_local_edges`,
  lib/std/tactic/cast.hthr), its map and source operations read off its
  type's indices as globals or locals; the composite through
  `Dyadic::rat_hom` is the nested move `cast_move` already made. The record
  is structural, so the local is recognised by checking the family's law at
  it with `A`, `B` set from a local map's type; the unifier now learns an
  index that is a class field read (`K.inv`, a projection-headed spine).
  `mono`
  at a class carrier now reads casts: `StrictOrder::le_of_same_l` and its
  three siblings are its push lemmas, applied with the dictionary in scope.
  `by mono_with([hx, hy])` proves `map(Dyadic::add(a, c).rat()) <= x + y`
  in the section above (lib/_tests/std/tactic/cast_tests.hthr,
  `local_hom_…`). Design: docs/casting-design.md §15. `ring`, `linarith` and
  `cast_from` at a class carrier are [[cast-reading-at-class-carrier]].
