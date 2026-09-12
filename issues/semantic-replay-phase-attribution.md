---
title: Attribute warm semantic replay cost by phase
status: open
labels: [tooling,performance,caching,measurement]
created: 2026-08-30
updated: 2026-09-12
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

## Log

- 2026-09-12: First per-phase reading of the warm x86 prefix replay (dev profile, furnace, 2026-09-12, the 18-module function_ir_x86 test prefix, Exact images): 5.4 s per process = image_recheck 4.5 s + image_decode 0.9 s + publication noise. The recheck is one serial check_global_ctx_extension per module (crates/elab/src/module_delta.rs) and four modules carry it: x86_64_block 1.58 s, x86_64 1.26 s (plus 0.56 s decode), x86_64_control_block 0.84 s, function_ir 0.51 s; the std prefix (list, bitvec, int, algebra) is ~0.15 s together. The measured dominant phase is therefore the kernel recheck of the arch modules, and the named lever is checking a replayed extension's declarations on the kernel worker pool the way the deferred gate does ([[parallel-kernel-gate]]): the pool is idle during replay today. Every test binary that replays this prefix pays the 5.4 s once; the x86 shards were re-merged on that datum ([[function-ir-x86-proof-scaling]] log).
- 2026-09-12: 2026-09-12: the measured dominant phase (kernel recheck) now runs on the kernel worker pool ([[parallel-kernel-gate]] log): warm 30-module native prefix recheck 4.66 s → 2.06 s wall at eight workers. What remains of it is the statement checks, which stay serial on the elaborator's thread; decode (0.7 s) is unchanged.
