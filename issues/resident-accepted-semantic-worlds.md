---
title: Reuse process-accepted semantic worlds across consumers
status: open
labels: [tooling,elaboration,performance,caching,design]
created: 2026-08-30
updated: 2026-08-30
---

`SemanticSession` safely reconstructs a world from disk images, but every new
session decodes and kernel-checks the same suffixes again. A daemon, editor,
test process or compilation pipeline commonly asks several questions of one
unchanged closure. Once this process and this kernel have accepted an image,
those consumers should share the resulting immutable committed world rather
than replaying 763 x86 bindings for each query.

This is not trusted disk replay. The resident entry is published only after
bounded decode, complete kernel-extension checking and atomic metadata replay
in the current process. Reuse is by semantic identity and immutable world
sharing, never by allocation address or unchecked deserialization.

## Acceptance

- Define the resident key, ownership and memory bounds; kernel/elaborator
  semantics and the complete accepted dependency identity must participate.
- A second consumer obtains an isolated elaborator over the accepted world
  without decoding or kernel-checking the shared prefix again.
- Consumer suffixes cannot observe one another's commits, diagnostics, gates,
  metrics or configuration.
- Add eviction/accounting or an explicit bounded owner so resident reuse
  cannot grow without limit.
- Measure repeated x86 inspection/test consumers against fresh safe replay.

## What it assumes from elsewhere

- **[[semantic-module-images]]** supplies checked deltas and immutable
  committed-state boundaries.
- **[[shared-semantic-test-fixtures]]** is the first concrete consumer and may
  establish a smaller test-only form before this general resident store.
- **[[semantic-cache-lifecycle]]** owns persistent-disk cleanup, not resident
  world lifetime.

