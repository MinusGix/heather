---
title: Frame theorem over separable worlds and per-resource protocols
status: open
labels: [effects,proofs,design]
area: interaction-trees
created: 2026-11-08
updated: 2026-11-09
---

A world is any function of the whole history, so a write to fd 1 may change
what fd 0 reads (a terminal). That is why `Io` is one world
(`docs/effects-capabilities-design.md` §1), and it is also why there is no
frame rule: "`f` only touches stdout, so what `g` reads is unaffected" is
false at some worlds (`docs/effects-locality-design.md` §3 N4). The note
(§5.3) makes locality a hypothesis about the world instead of a property of
the type.

## Scope

- Resources: a partition of commands (`key: LinuxCmd<Nat> → K`), starting
  with the standard descriptors and paths; how descriptors returned by
  `open` bind to paths through the history is part of the design.
- `World::Separable(key)`: the answer to a command depends only on the
  history restricted to its resource.
- Protocols on one resource (`Pipe(0, chunks)`, `Sink(1)`, a file's
  contents), conjoined across disjoint resources; `World::piped` shown to
  satisfy `Pipe ∗ Sink`.
- The frame theorem: at a separable world, a function with footprint in
  `S` (`Io::Only`, [[io-footprint-facts]]) has a meaning that, restricted to
  `S`, depends only on the world's protocol at `S`. One customer: `cat`'s
  "sent(1) = received(0)" under `Pipe(0) ∗ Sink(1)`, composed with a
  function that writes only fd 2.
- A negative control: the theorem does not apply at an echoing terminal
  world, and the proof says why (it is not separable).

## What it assumes from elsewhere

- **[[io-footprint-facts]]** owns `Io::Only`. Assumed here: only its
  statement.
- **[[wp-view-separating-product]]** is the machine-level analogue for
  memory; nothing is shared but the shape.

## Log

- 2026-11-09: 2026-11-09: commuting operations at disjoint resources (trace equivalence) is filed as [[effect-independence]], shared with a reordering pass.
