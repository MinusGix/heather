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
Cold gate wall time drops by about half; peak memory across children
rises by about a third (design §10).

## Left

- **Duplicate content caches are refused, not merged** (design §4 step 3):
  two sibling families over one foreign index type would each register its
  code, and the first world holding both refuses. The library has none.
  Keeping the first copy after a content-hash check is the sound merge, to
  build when a pair appears.
- **Building ahead replays every closure once** (design §12): each build
  process replays its module's closure, about a quarter more cold CPU than
  folder children racing for shared modules. A long-lived worker that
  builds several modules in turn, restarted before its rail, would replay
  less; the verdict store's Merkle walk is most of a replay. Width beyond
  three is memory-bound (design §8).
- **The early cutoff's registry digest** is still over the whole world under
  the module, now the closure's
  ([[early-cutoff-registry-and-order-granularity]]).

## Log

- 2026-10-30: Expected refusals have images (design §11): a `lib/_tests` module refused exactly as its directives say is published and replays for a judging session of the same build. The gate builds ahead (§12, `heather check --build-jobs`): every missing module in a process of its own, longest chain first, so no child's rail pays for another's module; the race this issue listed is gone. Warm gate about half the wall time; cold about a fifth longer than racing, a third shorter than the chain.
