---
title: Two iters related by a state relation refine each other
status: closed
labels: [itree,proofs]
area: interaction-trees
milestone: [it-library, hih-pl-first-program]
created: 2026-10-21
updated: 2026-10-22
---

A compiled program meets its source's tree; the facts users care about are
proved against a size-free spec (`lib/native/stream_filter_spec.hthr`'s
`tr_spec`), so each program also needs `Program::Implements(source, spec)`.
For `tr` that relates two `iter`s with different state shapes: the
source's environment (buffer, offsets) against the spec's `FilterAt`. The
library has no lemma for it, so today each such proof would be an
induction over traces by hand. Found while writing
`docs/native-effect-source-design.md` (§8).

## Scope

- A simulation lemma: given `R: A → A' → Type` such that, from related
  states, one pass of the source body either makes no call and lands in
  related states (or the same break), or makes one call whose image (sizes
  forgotten, `linux_trees`'s `forget`) the spec's pass makes, landing in
  related states, then the source's `iter` refines (or `Implements`) the
  spec's, at shifted fuel.
- Stated for any container morphism, so `Implements` over `linux`/`linux_spec`
  is one instance and plain `Refines` another.

## What it assumes from elsewhere

- **[[interaction-trees-container-model]]** owns `iter`, `Same`,
  `Program::Refines` and `refines_shift`.
- **[[native-linux-spec]]** owns `Implements`.

## Log

- 2026-10-22: Done (`lib/std/itree/itree_sim.hthr`, `docs/itree-simulation-design.md`). `ITree::Sim` is read off the source through a `TraceMap` (forward, source to spec) and a `Contract` (valid answers, owed debts); `sim_bind`, `sim_below` and `sim_trace` are its laws, and `sim_iter` is the loop rule: a pass from related states is simulated by one spec pass, or is silent and lands related to the spec's unchanged state, and the loops simulate each other at the same fuel. `Program::Refines` and Linux's `Program::Implements` are both instances (`refines_of_simulates`; `lib/std/os/linux/linux_trees_sim.hthr`'s `implements_iter`). A source pass that is several spec passes (cat's write loop) is not covered; that is [[native-source-cat-implements]]'s to state.
