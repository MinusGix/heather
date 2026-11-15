---
title: Tensors over shapes as data, with canonical structure computed
status: open
labels: [design,machine-learning]
area: machine-learning
milestone: [ml-layers]
created: 2026-10-21
updated: 2026-10-22
---

Design Heather's tensor representation for the ML area
(`docs/surveys/wick-survey.md` §3.2, §3.6). A shape is a value of an inductive
(named dimensions with sizes); the index type of a tensor is computed from
the shape; a tensor is a function on that index type, with a curried view
(`Fin seqLen → R[keyDim]`) as the default and a flat view beside it.

Everything Wick found by typeclass search and then fought (the pairing
tower, flattening charts, parameter types, `+`/`0` on parameter records) is
an ordinary function on the shape here, with one definitional answer each.
The scalar is always a parameter, never inferred from the carrier (Wick's
`FlatCarrier` collapse failed exactly there, `ARCHITECTURE.md` B3.2).

Questions to answer: how the shape code meets value parameters on
inductives; which laws hold by evaluation at a literal shape and which need
a proof at a neutral one; what derive generates for parameter records; and
which executable representation the native backend should get (arrays rather
than lists), and what that needs from the heap.

## What it assumes from elsewhere

- **[[big-operator-semantics]]** owns the sum notation. Assumed here: only
  that finite sums over a computed finite index type exist.
- **[[byte-memory-access-model]]** owns heap memory. Assumed here: only that
  a native array of scalars can eventually be allocated.

## Log
