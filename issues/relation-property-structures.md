---
title: Build reusable structures for relation properties
status: closed
labels: [stdlib,mathematics,relations,design]
created: 2026-09-02
updated: 2026-09-02
---

Make reflexivity, symmetry, transitivity, antisymmetry, irreflexivity, and
totality ordinary reusable theories indexed by a relation `R : A -> A -> Type`.
They are the common substrate for equality-like relations, orders, apartness,
rewriting, and semantic relations.

The first round should decide which properties deserve classes, which are
plain predicates, and whether named composites such as `Equivalence(R)` use
inheritance or canonical theory composition. Include converse and relation-map
probes so the API is not designed only for homogeneous equality.

No decision procedure belongs in these structures.

## Decisions from the first round

- The primitive properties are independent operation-indexed classes:
  `Reflexive`, `Symmetric`, `Transitive`, `Antisymmetric`, `Irreflexive`, and
  `Total`. Their fields have `rel_` prefixes, keeping projections unambiguous
  beside identity's global `refl`/`sym`/`trans` vocabulary.
- `Equivalence` is the first named composite and has no own fields. Multiple
  inheritance supplies its three canonical parent views; a concrete `Nat`
  instance proves child-to-parent resolution rather than registering three
  copies.
- Identity equivalence at an open carrier is an explicit
  `relid_equivalence<A>()`, not `instance<A>`. A bare type variable has no
  carrier head to own the canonical `A::Equivalence` global, and the resolver
  diagnosed that attempted design directly. Concrete carriers may register a
  dictionary when resolution is useful.
- Pullback preserves the three equality-like properties and their composite.
  `PreservesRelation` remains a plain predicate indexed by both relations and
  the map; its heterogeneous composition is the first morphism-shaped
  customer, without prematurely making morphisms classes.

## What it assumes from elsewhere

- **[[algebraic-theory-composition]]** owns automatic/canonical composition.
  This issue needs only an explicit spelling if that design is not ready.

## Log

- 2026-09-02: Filed as the layer beneath orders and setoids.
- 2026-09-02: First round LANDED in `std/relation_props`: six primitive property
  classes, field-free `Equivalence`, identity constructor plus a concrete
  canonical control, pullback, and heterogeneous relation-preserving
  composition. Focused acceptance is 5/5. The required full `scripts/test`
  reached 2,267 passes, including every relation/algebra/stdlib target, but was
  incomplete with 15 certgen signature-decoding failures (`a Nat that is not a
  numeral`). The same focused `certgen_emissions` failure reproduces unchanged
  on the concurrent `master` checkout, which does not contain this round;
  therefore it is an inherited kernel baseline failure, not relation residue.
  This issue's acceptance is complete and the tracker closes it rather than
  owning that unrelated regression.
- 2026-09-02: Moved the law-bearing hierarchy out of `std/relation` when the
  compiler's heavy FunctionIR x86 test exposed how little performance margin
  semantic-relation customers currently have. `std/relation_props` now owns
  the classes, pullbacks, and relation-preserving maps, while the established
  semantic module remains a lean dependency. A detached-base control later
  confirmed that the x86 target's Furnace SIGKILL is inherited even without
  the new hierarchy; the split is still the cleaner dependency boundary.
