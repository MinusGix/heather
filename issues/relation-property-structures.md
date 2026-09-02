---
title: Build reusable structures for relation properties
status: open
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

## What it assumes from elsewhere

- **[[algebraic-theory-composition]]** owns automatic/canonical composition.
  This issue needs only an explicit spelling if that design is not ready.

## Log

- 2026-09-02: Filed as the layer beneath orders and setoids.
