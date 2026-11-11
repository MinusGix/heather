---
title: Each library build child replays its imports: up to a quarter of the cold build step
status: open
labels: [performance,testing,cache]
area: infrastructure
created: 2026-11-11
updated: 2026-11-11
---

Every child of `heather check --build-jobs` replays its module's import closure before it elaborates the module, so the cold library build repeats the shared prefix once per module. Found while writing [[performance-overview-2026-11-11]]; the build step is [[module-dag-build]]'s.

## Measured

Release binary at #553 plus the name-record fix, quiet four-core cloud box, `--build-jobs 4 --build-only lib` into an empty store with `--build-times`:

- 424 modules, 215 s wall, 845 s of summed child time, parallelism 3.9.
- The chain that finished last holds 26 s of building and 189 s of waiting for a free job, so on four cores the step's length is the total work.
- Checking a module over the full store afterwards (its closure's replay plus its own) has a median of 0.35 s and sums to 54 s over every fourth module, so about 215 s over all 424. That bounds what the children spend replaying: up to a quarter of the step.
- The same library built as one process per gate folder (37 processes, which replay a shared prefix once per folder) took 790 s summed with `--timings` on, against 845 s without it for the per-module children.

## Directions

- A child that stays alive along a chain: after building `m` it holds `m`'s world, and any ready module whose closure is that world can be elaborated in place (`SemanticSession::check_held`'s `in_place` path already exists for one process).
- A fork server: one process holds the common prefix (`logic` through `common`, 6 s of builds that almost every module imports) and forks a child per module, which inherits the loaded world copy-on-write.
- Cheaper replay itself: on a warm showcase check, image decode is 39% and the interface hashes 24% of 0.46 s.

## Done when

The summed child time of a cold library build is within a tenth of the same build done in one process per folder.
