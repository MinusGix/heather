---
title: Corecursion up to friends, round 2 (indexed, polymorphic, bind-shaped)
status: open
labels: [codata,coinduction,elaborator]
area: interaction-trees
created: 2026-11-02
updated: 2026-11-02
---

Corecursion up to friends landed for unindexed codata and monomorphic
friends (`docs/codata-elaborator-design.md` §5.5): the carrier is the free
algebra of the friends over seeds and existing trees, a `Wf` tree, and each
friend's body is re-elaborated over it. The issue's three customers need
more than that:

- **Up-to proofs for `Bisim`/`Eutt`** (`docs/coitree-design.md` §7.6): a
  self-call under `trans`. Indexed codata: the free carrier becomes a family
  over the index (`Wf` → `IWf`, or a seed-style equation per node), and a
  friend's codata arguments sit at *different* indices from its result
  (`trans(r₁ : Bisim(a, b), r₂ : Bisim(b, c)) : Bisim(a, c)`), so the node's
  shape must carry the intermediate index `b`.
- **A direct coinductive `rec`** (`docs/partial-functions-design.md`):
  the non-tail call sits under `bind(t : CoTree<R>(E), h : R → CoTree<S>(E))`.
  `t` is of another instance than the result (the free carrier becomes
  multi-sorted: a node of `C_R` may hold children of `C_S`), `h` is a
  function into codata (a function-indexed child, so `Wf`'s `Vec` children
  no longer suffice), and `bind`'s `Ret(r) => h(r)` returns a *child's* node
  rather than an argument's, which `Wf` recursion supports (the child's `ih`
  is in hand) but friend mode refuses today.
- **Power series generic over a ring** (`issues/formal-power-series.md`):
  a friend `add<A: CommRing>` has a type parameter and a class binder.
  Friend mode would instantiate the friend's type parameters from the
  definition's codata type and its class binders by resolution at the call.

Smaller gaps, each refused with its reason today:

- friends whose parameter types mention other parameters (`E: Events` before
  `t: CoTree<R>(E)`);
- a friend calling another friend in its own step (the free algebra already
  has every friend's node; friend mode would accept a call to any friend of
  the site at a child);
- constructors nested above a call beside a friend (§5.4 with §5.5: a
  pending-node shape in the free algebra);
- a constructor with a call inside a friend's argument (the same pending
  node, as a leaf).

## What it assumes from elsewhere
- **`docs/codata-elaborator-design.md` §5.5** owns the round-1 carrier and
  friend mode. Assumed here: only that the step is structural recursion on
  the free carrier and friend nodes read their arguments' nodes from `ih`.
