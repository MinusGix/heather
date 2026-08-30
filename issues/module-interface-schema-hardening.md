---
title: Make module-interface projection changes reviewable and differential
status: open
labels: [tooling,elaboration,caching,robustness,testing]
created: 2026-08-30
updated: 2026-08-30
---

The projected module identity intentionally erases source spans, opaque proof
bodies and proof-provenance edges while retaining statements, transparent
bodies and every frontend registry visible to dependents. Rust's exhaustive
matches ensure that a new `DeltaEvent` is encoded somewhere; they cannot prove
that its chosen interface projection is observationally correct. A future
registry addition could therefore cause unsound reuse if omitted, or needless
invalidation if opaque data is retained.

## Acceptance

- Document a schema-review checklist beside `DeltaEvent` and the interface
  encoder: replay representation, dependent observability, opacity and
  invalidation controls must be answered for every new event/field.
- Add differential consumer fixtures for each event family or coherent group:
  change the producer fact and require either stable consumer identity or a
  miss according to its declared semantics.
- Keep source/replay downstream Ψ and lookup behavior equal for the complete
  registry-rich fixture.
- Make format/domain version changes explicit when projection semantics move.

## What it assumes from elsewhere

- **[[semantic-module-images]]** owns the current interface projection and
  registry-rich replay fixture.
- **[[relocatable-semantic-module-images]]** changes reference positions, not
  which semantic facts belong to the interface.

