---
title: Two iters related by a state relation refine each other
status: open
labels: [itree,proofs]
area: interaction-trees
milestone: [it-library, hih-pl-first-program]
created: 2026-10-21
updated: 2026-10-21
---

A compiled program meets its source's tree; the facts users care about are
proved against a size-free spec (`lib/stream_filter_spec.hthr`'s
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
