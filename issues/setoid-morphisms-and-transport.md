---
title: Transfer structure and theorems through setoid morphisms
status: open
labels: [stdlib,mathematics,setoids,automation,design]
created: 2026-09-02
updated: 2026-09-02
---

Grow from respectful functions to setoid homomorphisms, embeddings,
equivalences/isomorphisms, and explicit transport of predicates and algebraic
structure. Use concrete failures to distinguish operation lifting, predicate
respectfulness, theorem transfer, and wholesale structure transport.

The forcing customer is comparison between real presentations. The goal is
not to make arbitrary representation-specific theorems magically portable;
it is to make abstractly stated ordered-algebra results reusable once a
structure-preserving equivalence is proved.

## What it assumes from elsewhere

- **[[setoid-core-api]]** owns explicit equivalence and respectfulness.
- **[[setoid-auto-lifting]]** owns boxed-code proof generation.
- **[[real-presentation-comparison]]** owns which real maps are equivalences
  under which assumptions.

## Log

- 2026-09-02: Filed separately from auto-lifting so concrete mathematical
  transport determines what automation should eventually produce.
