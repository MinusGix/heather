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
([[library-gate-warmup-runs-alone]]). `docs/infrastructure/module-dag-design.md` replaces
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
  less; the verdict store's Merkle walk was most of a replay, and a
  canonical replay now skips it (design §13). The gate runs four wide
  (design §8); more than one process per CPU would only queue.
- **The early cutoff's registry digest** is still over the whole world under
  the module, now the closure's
  ([[early-cutoff-registry-and-order-granularity]]).

## Log

- 2026-10-30: Expected refusals have images (design §11): a `lib/_tests` module refused exactly as its directives say is published and replays for a judging session of the same build. The gate builds ahead (§12, `heather check --build-jobs`): every missing module in a process of its own, longest chain first, so no child's rail pays for another's module; the race this issue listed is gone. Warm gate about half the wall time; cold about a fifth longer than racing, a third shorter than the chain.
- 2026-10-30: A replay that rechecked clean over its own canonical world is vouched for whole next time (design §13): one verdict keyed by build, world identities and image content, so the per-binding Merkle walk is skipped. Moved replays keep the per-binding path. Warm tactic-test module about a sixth faster; decode-bound modules unchanged.
- 2026-10-30: Moved replays are vouched for whole too (design §13): the key adds the world the stored positions were counted in beside the one the image is moved into, which fixes the moved delta, so nothing about `relocate` is trusted beyond determinism. All three move sites key their replays. Warm `mono_tests` (release, cloud, by hand, 4 interleaved pairs): 4.51–4.69 s → 3.69–3.79 s; per-declaration questions 780 → 0, Merkle walk 0.84 s → 0. The composition moves are now timed as `image_relocate_ns`, and they are 2.3 s of the 3.7 s left ([[warm-replay-relocate-cost]]).
- 2026-10-30: The gate builds and checks four wide (design §8). Memory was no longer the bound: since building ahead each build process holds one closure (largest just under 2 GB) and the summed peak stays under 3 GB at four jobs as at three. `heather check` tells its session the load (`SemanticSession::expect_load`), which drops a module's world once nothing left imports it and its delta once nothing left holds it; folder children's peaks drop by an eighth to a quarter, build processes are unchanged. Cold build step about a fifth shorter.
