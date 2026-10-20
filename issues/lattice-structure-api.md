---
title: Develop lattice structures from orders and indexed operations
status: open
labels: [stdlib,mathematics,order,algebra]
area: mathematics
milestone: [math-classes]
created: 2026-09-02
updated: 2026-09-02
---

Develop meet/join semilattices, lattices, bounded lattices, and the connection
between their algebraic laws and order universal properties. Both the relation
and operations should be explicit indices, allowing multiple orders or
operations on one carrier.

Begin with the already proved `Nat` and `Int` min/max laws, then add a product
control. Decide from those probes whether order-derived and algebraically
presented lattices are separate interfaces connected by constructors, or one
canonical theory.

## What it assumes from elsewhere

- **[[mathematical-order-hierarchy]]** owns preorder/partial-order structure.
- **[[algebraic-theory-composition]]** owns canonical multi-parent layering.

## Log

- 2026-09-02: Filed as a concrete test of relation-plus-operation theories.
