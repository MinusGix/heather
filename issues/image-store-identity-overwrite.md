---
title: Let two compiler builds share an image store without overwriting each other
status: open
labels: [tooling, infrastructure, cache]
area: infrastructure
created: 2026-11-04
updated: 2026-11-04
---

A module image's key (`ModuleCacheKey`, `crates/cache/src/module_image.rs`)
leaves out the build that wrote it; the build's `SemanticsIdentity` sits in the
header. Under the exact policy an image with another identity is a miss, and
the rebuilt image is written to the same key, replacing it.

With several checkouts sharing a store through `HEATHER_CACHE_DIR`
([[shared-cache-dir]]), two worktrees whose kernel, syntax or elaborator
sources differ therefore overwrite each other's image of every library module
on each exact run, and both stay cold. (Under accept-stale they share, which
is why the fast and pr lanes are unaffected.)

Wanted: images of the same key from different identities coexist (the
identity in the path, or a small per-key set), the exact policy picks its own,
and eviction treats each identity's images like any other. The `.latest` and
`.src` pointers already tolerate this; they only lose hits.

## What it assumes from elsewhere

- **[[shared-cache-dir]]** owns where the store lives. Assumed here: only that
  several checkouts may share it.

## Log

- 2026-11-05: gardener: cites a file it shares with [[testing-architecture]] (`crates/cache/src/module_image.rs`).
