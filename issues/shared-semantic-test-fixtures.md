---
title: Share safely accepted semantic prefixes across expensive test fixtures
status: closed
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

## Log

- 2026-08-30: Implemented `semantic_test_base` in the shared elaborator test
  support. It accepts an explicit dependency-first source list, uses the
  public `SemanticSession` and `target/semantic-test-images`, prints every
  cache rejection, and returns an elaborator explicitly sealed with
  `NoGate`. An isolated-directory control corrupts an image, observes the
  loud rejection/rebuild, requires equal Ψ and checks a fresh consumer suffix.

  X86 uses the helper for ordinary tests while its phase/value profiling
  environment variables retain the original source-only route. The exact
  target passed cold in 171.88 seconds and warm in 143.94; base-only warm
  replay of all 13 modules is 7.38 seconds. The remaining roughly 136 seconds
  belongs to freshly checked execution, decoder and negative-control
  suffixes, so semantic setup reuse is helpful but not their owner.

  The larger suite win is Omega. The core, logic and reconstruction binaries
  and the division-scaling shard now replay the same nine-module prefix;
  `omega_div_mod` deliberately remains source-only as the full-prefix
  backstop. Warm exact-target results, all green with nine safe module
  replays: core 160.06 seconds, logic 67.64, reconstruction 40.01 and scaling
  98.12. Logic's first cold combined prefix+shard run reached the fixed rail
  and was killed at 312 seconds after atomically publishing the missing Omega
  image; the immediate warm rerun passed. This is precisely the cross-binary
  multiplier the shared store removes without weakening fresh suffix checks.

  Cold scheduling is explicit rather than hopeful. `semantic_x86_warmup` and
  `semantic_omega_warmup` contain only their prefix loads; `scripts/test` runs
  the applicable target first for focused x86/Omega invocations and both
  before an unfiltered parallel suite. Each process receives the ordinary
  memory/CPU rail. Thus an invalidated Omega prefix may spend its roughly
  prefix-sized budget once, then the acceptance shard starts with a fresh CPU
  budget and safe replay. Warm warmups measured 7.28 seconds for all 13 x86
  modules and 0.93 seconds for all nine Omega modules. A runner-driven warm
  reconstruction check then passed in 34.92 seconds.

  Closed: the reusable seam, corruption control, x86 conversion, profiler
  escape hatch, Omega family conversion, source-only backstop and measured
  exact targets are all present. General multi-consumer in-process reuse is
  separately owned by [[resident-accepted-semantic-worlds]].
