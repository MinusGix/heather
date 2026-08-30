---
title: Share safely accepted semantic prefixes across expensive test fixtures
status: open
labels: [testing,tooling,elaboration,performance,caching]
created: 2026-08-30
updated: 2026-08-30
---

Large integration targets need an in-process elaborator after loading their
library prefix. The x86 harness already consolidates its assertions behind
one `x86_64_suite`, but its setup still source-elaborates the complete
13-module closure whenever that test binary runs. Other proof families use a
trusted declaration cache to reduce repeated gates while still parsing and
elaborating the prefix.

The earlier closed [[elaborator-snapshot-across-test-binaries]] rejected
semantic-state serialization because no complete, checked representation
existed. [[semantic-module-images]] has now supplied that representation and
a public `SemanticSession`: warm x86 safe replay is 5.44 seconds rather than
66.29 seconds from source. Test tooling should consume it directly and fork
the resulting immutable world for fresh theorem/control suffixes.

## Acceptance

- Add a test-support API which loads a topologically ordered source closure
  through `SemanticSession`, stores images under `target/`, and returns an
  ordinary in-process `Elaborator` with no trusted declaration gate left
  installed.
- Convert x86 first. Preserve its single base construction, optional metrics,
  negative controls and fresh cloned suffixes byte-for-byte.
- A cold run remains a complete source/kernel check and publishes images; a
  warm run bounded-decodes and kernel-checks every imported suffix before the
  test sees metadata.
- Cache rejection is loud, non-fatal and followed by source rebuild.
- Record cold/warm exact-target wall time and run the full x86 target under
  `scripts/test`; do not weaken the mutation or negative controls.
- Document the extension seam for other expensive test families without
  mechanically converting every fixture.

## What it assumes from elsewhere

- **[[semantic-module-images]]** owns image soundness and invalidation.
- **[[resident-accepted-semantic-worlds]]** owns later reuse across several
  consumers in one process; this issue needs only one accepted test base and
  cheap immutable clones.
- **[[generated-term-oracle-controls-not-convertible]]** records why the x86
  suite was consolidated and why its controls must remain freshly checked.

