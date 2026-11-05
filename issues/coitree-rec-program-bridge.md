---
title: CoTree::rec refines Program::rec both ways
status: open
labels: [coinduction,itree,native]
area: interaction-trees
created: 2026-10-31
updated: 2026-10-31
---

`CoTree::rec` (`lib/std/itree/coitree_rec.hthr`, docs/partial-functions-design.md
§4.3) has no refinement theorem against the fuelled `Program::rec`
(`itree.hthr`), the way `CoTree::iter` has `iter_refines`/`iter_refined`
against `Program::iter` (`coitree_bridge.hthr`, docs/coitree-design.md §8.2).

## Scope

- `CoTree::rec_refines`/`rec_refined`: for a finite body,
  `CoTree::program(CoTree::rec(D, E, of_tree ∘ body, d))` and
  `Program::rec(D, E, body, d)` refine each other.
- The finite side's `mrec` goes one `mrec_layer` per unit of fuel and
  re-enters through `Tau(mrec(m, bind(body(d), k)))`; the coinductive side is
  a loop over the pending tree. Expect the depth-to-fuel direction to read
  the pending tree's binds through `bind_traces` (§8.3) and the other to need
  a hypothesis named as a type, as `IterFrom` was.

## Why it waits

Only non-tail recursion at run time needs it: a tail-recursive `partial`
function is `CoTree::iter`, which the bridge already covers, and non-tail
native recursion needs a call stack (`nh-heap`). Take it with the first
native customer of non-tail partial recursion.

## Log

- 2026-11-05: gardener: cites a file it shares with [[codata-up-to-friends-round-2]] (`docs/coitree-design.md`).
