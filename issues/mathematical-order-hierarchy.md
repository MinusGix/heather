---
title: Separate the mathematical order hierarchy from comparison
status: open
labels: [stdlib,mathematics,order,traits]
created: 2026-09-02
updated: 2026-09-02
---

Define preorder, partial-order, and linear-order theories over an explicitly
indexed relation. The hierarchy should be proposition-first and contain no
decidability field. Exercise it at `Nat`, `Int`, a product order, and one open
carrier.

Inventory which existing `Cmp` consumers require only order laws and which
genuinely select a branch. Keep executable comparison as an orthogonal layer;
constructive real orders must be able to inhabit this hierarchy without
claiming decidability.

## What it assumes from elsewhere

- **[[relation-property-structures]]** owns the primitive relation laws.
- **[[decidable-relations-and-comparison]]** owns executable comparison.

## Log

- 2026-09-02: Filed to prevent `Cmp` from becoming the mathematical meaning of
  order merely because it was the first generic consumer.
