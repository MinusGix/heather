---
title: Bridge coinductive trees to the fuelled programs
status: closed
labels: [codata,coinduction,itree,library]
area: interaction-trees
milestone: [it-coinductive,it-program-bridge]
created: 2026-10-22
updated: 2026-10-24
---

`CoTree::program(t)` is the `Program` of `t`'s approximations
(`lib/std/itree/coitree.hthr`), and the finite library has its own fuelled
programs (`Program::iter`, `Program::rec`, `lib/std/itree/itree_trace.hthr`).
Nothing yet says they agree.

Done when:
- `CoTree::program(CoTree::iter(body, a))` and `Program::iter` refine each
  other (both directions of `Program::Refines`), when the body is a finite
  tree embedded as a coinductive one; the same for `bind`.
- Bisimilar trees give programs that refine each other (`Bisim::approx`
  gives `Same` at every depth; `ITree::refines_of_same` closes it).
- Optionally, an embedding `ITree → CoTree` (a `Cut` has no coinductive
  counterpart, so it maps to `spin` or is excluded) with approximation as its
  left inverse at enough depth.

## What it assumes from elsewhere
- **[[coitree-library]]** owns `CoTree::program` and `Bisim::approx`.
  Assumed here: only their statements.

## Log

- 2026-10-22: Bisimilar trees give programs that refine each other (`Bisim::refines`), and so do trees equivalent up to taus (`Eutt::refines`, `Eutt::refined`), all in `lib/std/itree/coitree_eutt.hthr`. Still open: `CoTree::program(iter(…))` against `Program::iter`, and the optional embedding.
- 2026-10-24: Done (`lib/std/itree/coitree_bridge.hthr`, `docs/itrees/coitree-design.md` §8). `CoTree::of_tree` embeds a finite tree (`Cut` as `spin`) with exactly its traces; `CoTree::iter_refines`/`iter_refined` relate the fuel-free loop over an embedded body to `Program::iter` both ways; `CoTree::bind_refines`/`bind_refined` relate `program(bind(t, h))` to `Program::bind` of the programs for any coinductive trees. Approximation is not a left inverse of the embedding at a fixed depth (infinitely branching calls), so the embedding is stated by traces.
