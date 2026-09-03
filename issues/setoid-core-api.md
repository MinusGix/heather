---
title: Add a small operation-indexed setoid core
status: open
labels: [stdlib,mathematics,setoids,relations]
created: 2026-09-02
updated: 2026-09-02
---

Introduce the minimum explicit API for reasoning modulo an equivalence
relation: a setoid/equivalence structure indexed by its relation, unary and
binary respectfulness predicates, identity equality as a control, and basic
composition lemmas.

Keep this round manual. It should be validated by unreduced rationals and one
function-valued or proof-bearing representation before adding bundles,
notation, coercions, or lifting automation.

## What it assumes from elsewhere

- **[[relation-property-structures]]** owns equivalence-relation laws.
- **[[setoid-auto-lifting]]** owns future code-driven automation. Assumed here:
  no automation is required for the first API.

## Log

- 2026-09-02: Filed as a quotient substitute at abstraction boundaries, not a
  replacement for ordinary identity throughout the library.
