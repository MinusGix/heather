---
title: Compose algebraic theories canonically through classes
status: open
labels: [stdlib,mathematics,traits,design]
created: 2026-09-02
updated: 2026-09-02
---

Design how law-bearing classes compose before the arithmetic hierarchy grows.
Heather's operation-indexed classes avoid nominating one operation per carrier,
but a semiring-sized theory still has several useful parents, diamonds, and
possibly no fields beyond those parents. The goal is a dependency graph of
small theories rather than a copied bundled hierarchy.

Probe declared intersections/aliases, canonical parent projection, diamond
sharing, and explicit child construction. Do not let resolution assemble an
arbitrary child from propositionally matching parents: proofs are relevant and
two such assemblies need not be convertible. If special class support is
needed, it should express canonical theory composition generally.

Acceptance is a design plus small class probes with two operations, a diamond,
a field-free composite, and explicit first-class packaging as the control.

## What it assumes from elsewhere

- **[[operation-indexed-classes]]** owns value indices and canonical instance
  identity. Assumed here: operations remain indices.
- **[[class-alias-roles]]** owns elaborator-visible roles for class aliases.
  Assumed here: aliases are a candidate, not the decided implementation.

## Log

- 2026-09-02: Filed from the algebra/reals API discussion. Algebra is important
  enough to force general class-composition support, but not arithmetic-only
  magic.
- 2026-09-02: Adversarial first probes establish that Heather's existing
  composition is already strong for a single fiber: empty composite classes
  work, a shared ancestor in a diamond is synthesized once, its projections
  agree definitionally, and an open child dictionary upcasts to its parents.
  Resolution is intentionally one-way: a declared child supplies parents, but
  independently registered parents are never assembled into an undeclared
  child. This preserves proof relevance and keeps theory composition explicit.
- 2026-09-02: The two-operation probe found a real safety bug. Repeating one
  indexed parent class at distinct fibers, directly or through two parents,
  was accepted but deduplicated by class name, silently discarding the second
  structure. The elaborator now distinguishes identical-fiber diamonds from
  distinct-fiber repetition: the former still collapses, while the latter is
  refused with both fibers named. Explicit dependent-record packaging is
  tested as the honest control and preserves both dictionaries.
- 2026-09-02: Role-bearing class aliases are not the answer to multi-operation
  composition. They are intentionally transparent views of one class fiber;
  using them to manufacture distinct storage would recreate parallel
  hierarchies under another spelling. The remaining design choice is between
  the earlier qualified-flat-slot direction and named parent dictionaries.
  Named parents (`extends Monoid<A>(add) as additive`) could lower to an actual
  `additive: Monoid<A>(add)` component: upcast projects the exact dictionary,
  collisions are naturally addressed as `s.additive.unit`, and unique-parent
  member dispatch can remain automatic. This revises the old assumption that
  `as` must merely rename copied flat fields; implementation waits for this
  representation choice to be agreed rather than baking it into the safety
  fix.
- 2026-09-02: The focused composition corpus is 6/6. Full Furnace
  `scripts/test` is 2,300 passed, zero failed, and five ignored, including the
  complete operation-indexed class, trait, algebra, and order suites. The issue
  remains open for qualified-parent representation and semiring-shaped
  acceptance rather than conflating that design with the landed refusal.
