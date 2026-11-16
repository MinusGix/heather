---
title: ring, linarith and cast_from at a class carrier
status: closed
labels: [tactics,casting,algebra]
area: tactics
created: 2026-10-31
updated: 2026-10-31
---

[[cast-reading-through-local-morphism]] made a morphism in scope an edge,
and `mono` reads casts through it at a class carrier
(`section<K: OrderedField(…)>(…, hom: OrderedRingHom<Rat, K>(…))`). The
other cast readers do not run at a class carrier at all, morphism or not:

- `ring` and `linarith` (crates/elab/src/ring.rs, `Carrier::Rel`) read a
  `≈` carrier only through a `CommRingOfInt` instance, a combined class
  ([[casting-standard]] §5.6 retires those). At `K` they need the class's
  operations as the ring, and the integers either read through the derived
  map out of `Int` or handed in as a morphism parameter (§5.6's open
  question). Their edges are the Rust `EDGES` table, by global names.
- `cast_from` / `cast_to` (lib/std/tactic/cast.hthr) find their carrier in
  `cast_carriers()` by global names (`Rat::Same`, `Rat::le_respects`, …)
  and build the carried proof by raw application of those lemmas. At a
  class carrier the relations are locals and the lemmas are `StrictOrder`'s
  with the dictionary as a premise: the carrier would be read off the
  dictionary in scope (as `mono_class_carrier` does) and the lemmas
  `apply`'d (as `mono_push_applied` does).

Wanted when a generic proof needs more than `mono`: the interval
containment round ([[interval-containment-once-over-ordered-field]]) is
expected to need only `mono`.

## Log

- 2026-10-31: LANDED for ring, linarith and nlinarith: at a class carrier the ring is the section's own operations (`semiring::CommRing::with_ints`, `ordered_field::OrderedField::with_ints` build the `…OfInt` dictionary from `K`'s class), integers read through the derived `semiring::Ring::int_cast` (no morphism parameter needed: Int is initial), and a morphism in scope is an edge of both (add, mul, sub, neg, 0, 1, composites through `Dyadic::rat_hom`). Probes in lib/_tests/std/tactic/{ring,linarith,cast}_tests.hthr; docs/language/casting-design.md §16. cast_from/cast_to split to [[cast-from-at-class-carrier]].
