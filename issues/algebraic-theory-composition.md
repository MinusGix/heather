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
