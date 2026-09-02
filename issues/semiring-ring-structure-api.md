---
title: Add a minimally factored semiring and ring API
status: open
labels: [stdlib,mathematics,algebra,traits]
created: 2026-09-02
updated: 2026-09-02
---

Add the first two-operation algebraic theories without importing a large
pre-existing hierarchy wholesale. Candidate factors include additive and
multiplicative monoids, distributivity as its own theory indexed by both
operations, and zero annihilation. `Ring` should reuse the additive group
rather than repeat inverse laws.

Use `Nat` and `Int` as the primary instances and prove generic finite-sum or
polynomial identities that actually consume the intermediate layers. Record
any missing weaker theory demonstrated by a consumer instead of adding every
possible nonunital/nonassociative variant in advance.

## What it assumes from elsewhere

- **[[algebraic-theory-composition]]** owns how the parents compose.
- **[[big-operator-semantics]]** owns eventual notation and domain-sensitive
  big-operator meaning.

## Log

- 2026-09-02: Filed with distributivity treated as a natural independent
  structure, not an incidental field buried in `Semiring`.
