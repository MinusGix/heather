---
title: partial fn denotes a coinductive computation, so specifications carry no fuel
status: open
labels: [design,termination,coinduction,native]
area: language
created: 2026-10-31
updated: 2026-10-31
---

Item 5, part 2, of the fundamental-improvements memo of 2026-10-31 (Claude Doc, https://claude.ai/artifact/Y2Jo9y9Mgd52QdguvaL43s): a function that may not terminate says `partial`
and denotes a coinductive computation, instead of taking a fuel argument that
its theorems then have to mention. Minus has said fuel should stay out of
statements (the itree rounds).

## Scope

- `partial fn` lowers into the coinductive tree library: a `Delay`, or an
  `ITree` with no events (`docs/coitree-design.md`). Its theorems are about
  convergence, through the coinductive↔fuelled bridge (`coitree_bridge.hthr`).
- `runtime fn` programs that loop until EOF or forever use it
  ([[runtime-fn-default-setup]]).
- Fuel stays where a budget is part of the meaning (a tactic's search
  depth). The sequencing design's `while … fuel` remains the explicit form.

## Done when

The decimal formatter or another fuel-specified library function is
restated without fuel in its statement, and a `partial` runtime loop
compiles under the default setup.

## Log

- 2026-10-31: Assessed in `docs/partial-functions-design.md`. The
  coinductive library already has everything except `CoTree::rec`. A probe
  builds it as a loop over the pending tree (`iter`, Coq's `interp_mrec`):
  its unfolding laws hold by `refl` at open arguments, runs at literals check
  by a count and `refl`, and the cost is linear in calls. The note proposes
  `partial fn f(x: A) → B` as `f : A → CoTree<B>(E)`, with tail recursion
  lowered to `iter`, and the general case to `rec`; proofs go through
  library rules (`Returns`, fixpoint induction, a measure rule,
  `Partial::get`). It also proposes changing "done when": the decimal
  formatter's fuel is a termination witness (its fix is
  `unfolding-computed-scrutinee` and `while … decreases`), so the customer
  should be the kernel model's `Tm::whnf`, whose divergence is real. Three
  rounds in §6, for Minus's decision.
