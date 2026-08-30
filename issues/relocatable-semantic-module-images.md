---
title: Relocate semantic module images across equivalent dependency worlds
status: open
labels: [tooling,elaboration,caching,performance,design]
created: 2026-08-30
updated: 2026-08-30
---

The current image format stores absolute Ψ positions and consequently keys a
module by the complete ordered accepted loader prefix. An unrelated earlier
module, a different topological order or composition into an equivalent world
therefore prevents reuse even when every direct semantic dependency is
unchanged. It also blocks useful parallel construction of independent module
suffixes.

Relocation is a representation project, not a cache-key tweak: kernel globals
and all correlated frontend registry positions must be rewritten coherently
and then checked against the destination dependency telescope. The current
exact-prefix rule remains the sound baseline until measured invalidation or
parallel scheduling justifies that surface.

## Acceptance

- Inventory every absolute global position in kernel terms, surface schemas,
  scopes and semantic registries; no pointer/address identity participates.
- Define position-independent external references and a total, bounded linker
  into an already accepted destination world.
- Reject missing, ambiguous or interface-mismatched dependencies before any
  metadata publication.
- Differentially compare relocated replay with fresh source elaboration under
  reordered and unrelated-prefix worlds.
- Measure a real invalidation or parallel-build workload before replacing the
  exact-prefix format.

## What it assumes from elsewhere

- **[[semantic-module-images]]** supplies the safe exact-prefix baseline.
- **[[parallel-checking-and-caching]]** owns scheduling and the broader trust
  architecture; relocation is one prerequisite, not parallelism itself.
- **[[module-interface-schema-hardening]]** owns downstream-observable facts.

