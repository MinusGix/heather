---
title: Develop apartness as a first-class constructive relation
status: open
labels: [stdlib,mathematics,logic,relations]
created: 2026-09-02
updated: 2026-09-02
---

Define apartness and its useful variants independently of decidable inequality
and strict order. Probe irreflexivity, symmetry, cotransitivity, compatibility
with a setoid relation, and tightness (`not (x # y)` implying equivalence) as
separate laws rather than assuming one maximal definition.

Concrete customers should include rationals, a constructive ordered-field
interface, and a real presentation where apartness has positive witness data.

## What it assumes from elsewhere

- **[[relation-property-structures]]** owns primitive relation laws.
- **[[setoid-core-api]]** owns the equality-like relation paired with tight
  apartness.

## Log

- 2026-09-02: Filed because constructive apartness is mathematical structure,
  not a synonym for `Decide<x != y>`.
