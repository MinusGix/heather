---
title: Separate the mathematical order hierarchy from comparison
status: closed
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

## Decisions from the first round

- The non-strict hierarchy is `Preorder<R>` (reflexive, transitive),
  `PartialOrder<R>` (plus antisymmetry), then `LinearOrder<R>` (plus
  propositional totality). All three are indexed by the relation and add no
  duplicate law fields beyond their declared parents.
- `Nat` and `Int` each register one `LinearOrder` dictionary. Canonical parent
  synthesis makes the same declaration answer preorder and partial-order
  constraints; there are no repeated instances at weaker layers.
- Componentwise products stop at `PartialOrder`. Even when both factors are
  linear, the product need not be, which is the concrete reason the weaker
  layer exists rather than merely hierarchy convention.
- Pullback along any function preserves a preorder. Pulling back a partial
  order requires `Injective(f)` explicitly, because antisymmetry first proves
  equality only after applying `f`.
- `Cmp` has one consumer family in `std/algebra`: `max_of` and its two laws.
  The function genuinely branches via `le_dec`, so it remains in the
  executable-comparison layer and nothing migrates in this round.
- Strict orders are deferred. Defining constructive `<` as `<=` plus
  disequality would prejudge its relationship with apartness and locatedness;
  [[apartness-structures]] should supply the next forcing examples.

## What it assumes from elsewhere

- **[[relation-property-structures]]** owns the primitive relation laws.
- **[[decidable-relations-and-comparison]]** owns executable comparison.

## Log

- 2026-09-02: Filed to prevent `Cmp` from becoming the mathematical meaning of
  order merely because it was the first generic consumer.
- 2026-09-02: First implementation added `std/order`, canonical `Nat`/`Int`
  instances, componentwise products, and injective pullbacks. `pair_ext` lives
  with `std/pair`, while the generally useful `Injective` predicate lives with
  `std/relation_props`. Focused Furnace acceptance is 3/3. The required full
  `scripts/test` completed 2,288 tests with zero failures, including both new
  stdlib targets and all repaired certgen targets, but reported INCOMPLETE when
  `function_ir_x86` was SIGKILLed at 150.20 seconds. An isolated run of that
  binary fails at the same resource boundary in a detached worktree at the
  untouched base commit `0059fbf`, so this is an inherited Furnace limit and
  not an order-hierarchy regression.
- 2026-09-02: Rebased onto `59949d1`, which shards the FunctionIR x86 suite.
  The required full Furnace `scripts/test` is now complete: 2,293 passed, zero
  failed, and five ignored. The order suite is 3/3 and the relation suite is
  5/5 within that run.
