---
title: Build library modules in dependency order, keyed by their import closures
status: open
labels: [testing,performance,images]
area: infrastructure
created: 2026-10-30
updated: 2026-10-30
---

The library gate's children followed one linear world order, because a
module's image was keyed by every module loaded before it
([[library-gate-warmup-runs-alone]]). `docs/module-dag-design.md` replaces
the world with closure worlds: a module elaborates over its own import
closure in a canonical order, its image is keyed by that closure's
identities (a Merkle DAG over the import graph), and images built apart
are moved into any world that needs them. Nominal tags hash the qualified
name ([[nominal-tags-from-declaration-identity]]), and registries are
visible only through imports, so an image means one thing.

Built 2026-10-30 (design §9): independent modules build in parallel across
the gate's children, which set aside a module another process is building.
Cold gate wall time drops by about two fifths; peak memory across children
rises by about a third (design §10).

## Left

- **Duplicate content caches are refused, not merged** (design §4 step 3):
  two sibling families over one foreign index type would each register its
  code, and the first world holding both refuses. The library has none.
  Keeping the first copy after a content-hash check is the sound merge, to
  build when a pair appears.
- **The gate's folder order** stays `World::folders`; a simulation found no
  order worth the rail risk. Width beyond three children is memory-bound
  (design §8).
- **The early cutoff's registry digest** is still over the whole world under
  the module, now the closure's
  ([[early-cutoff-registry-and-order-granularity]]).
