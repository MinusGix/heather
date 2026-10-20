---
title: Bound and inspect the persistent semantic module cache
status: open
labels: [tooling,caching,performance,robustness,cli]
area: infrastructure
created: 2026-08-30
updated: 2026-08-30
---

Semantic images are content-addressed and atomically published, so stale
entries are harmless misses, but the store currently grows forever. Format
and key-domain changes also leave obsolete generations behind, while the
directory name `modules-v1` no longer communicates the version-3 envelope.
Serious editor, test and compiler use needs bounded, observable housekeeping.

## Acceptance

- Provide total bytes, entry counts, format/key generation and useful age or
  last-use information through a cache inspection command or stable API.
- Define a bounded eviction/garbage-collection policy which never affects
  correctness and tolerates concurrent readers and writers.
- Clean obsolete generations deliberately; do not infer validity from a
  directory name or delete unknown user files.
- Stress concurrent publication, eviction and corruption recovery.
- Keep cache maintenance optional and non-fatal to a check whose semantic
  answer already stands.

## What it assumes from elsewhere

- **[[semantic-module-images]]** owns atomic publication and format identity.
- **[[resident-accepted-semantic-worlds]]** owns in-memory lifetime; this
  issue is persistent storage only.

