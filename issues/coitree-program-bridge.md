---
title: Bridge coinductive trees to the fuelled programs
status: open
labels: [codata,coinduction,itree,library]
area: interaction-trees
milestone: [it-coinductive]
created: 2026-10-22
updated: 2026-10-22
---

`CoTree::program(t)` is the `Program` of `t`'s approximations
(`lib/std/coitree.hthr`), and the finite library has its own fuelled
programs (`Program::iter`, `Program::rec`, `lib/std/itree_trace.hthr`).
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

- 2026-10-22: Bisimilar trees give programs that refine each other (`Bisim::refines`), and so do trees equivalent up to taus (`Eutt::refines`, `Eutt::refined`), all in `lib/std/coitree_eutt.hthr`. Still open: `CoTree::program(iter(…))` against `Program::iter`, and the optional embedding.
