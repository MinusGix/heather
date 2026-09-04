---
title: Relocate semantic module images across equivalent dependency worlds
status: open
labels: [tooling,elaboration,caching,performance,design]
created: 2026-08-30
updated: 2026-09-04
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

## Log

- 2026-09-04: Measured the invalidation workload this issue asks for (2026-09-04, release CLI, --cache-dir, ulimit-wrapped). Appending one trivial theorem to nat.hthr (the most-edited stdlib file: 31 commits since 2026-08-05) costs downstream: order closure 0.35 s warm -> 1.2 s (480 decl-cache hits, 9 modules re-elaborated); x86 model closure 4.5 s warm -> 18.2 s (403 decl-cache hits, zero kernel); omega closure 0.37 s warm -> 64.8 s, i.e. the full cold cost (61 s), because omega's cost is the omega/CutSat tactic search re-running, which no declaration-cache hit avoids. A proof-only edit in nat invalidates nothing downstream (0.4 s). Exact-prefix keying is therefore the dominant inner-loop cost for the actual churn pattern (edits land in nat/algebra/int, everything heavy sits downstream). Possible cheaper first slice to scope before full position-independent references: per-dependency range relocation (each dependency module's old Ψ range -> new range, valid when the referenced declarations' interface hashes are unchanged), since an append at the end of an upstream module shifts every later range uniformly.
