---
title: Attribute warm semantic replay cost by phase
status: open
labels: [tooling,performance,caching,measurement]
created: 2026-08-30
updated: 2026-08-30
---

A warm x86-64 closure now safely replays all 13 modules in 5.44 seconds, down
from 66.29 seconds cold. That is already usable, but the remaining time is an
aggregate of storage reads, checksums, bounded decode and validation,
interface projection, kernel extension checking, metadata publication and
warning rendering. Optimizing the largest imagined component without
attribution would repeat earlier unproductive performance rounds.

## Acceptance

- Add opt-in, near-zero-disabled-cost timing around read/checksum, decode and
  validation, interface hashing, kernel extension checking, metadata replay
  and diagnostics preparation.
- Report per-module and closure totals without changing ordinary CLI output.
- Measure warm x86-64 and one smaller closure in release mode under
  [[perf-tracking-consistent-environment]].
- Name the next optimization only from the measured dominant phase; retain no
  instrumentation that materially moves the uninstrumented warm path.

## What it assumes from elsewhere

- **[[semantic-module-images]]** owns the image format and current 5.44-second
  x86 point.
- **[[resident-accepted-semantic-worlds]]** may remove repeated work across
  consumers, but should not guess which single-replay phase is expensive.

