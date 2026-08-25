---
title: Run independent test binaries in bounded parallel under suite limits
status: open
labels: [testing,tooling,performance,parallelism]
created: 2026-08-25
updated: 2026-08-25
---

Cargo runs Heather's many integration-test binaries sequentially. The runner
sets `RUST_TEST_THREADS=2`, which parallelizes tests only *inside* the current
binary; dozens of independent 15–67 second targets therefore serialize even
when the machine has idle cores.

Add bounded target-level parallel execution without weakening the resource
and failure-reporting guarantees in `scripts/test`. `cargo-nextest` is not
currently installed and adopting it is a dependency/toolchain decision; a
first-party scheduler would need to discover Cargo-built executables, retain
doctests and filters, capture output deterministically, and aggregate killed
processes correctly. Choose between those shapes only after measuring memory
and CPU contention on two representative elaborator-heavy binaries.

## Acceptance

- Run at least two independent integration targets concurrently with an
  explicit, conservative job bound.
- Preserve a per-process CPU/stack/address-space rail and add a documented
  aggregate-memory argument; two 4 GiB children are not automatically safe.
- Preserve exact pass/fail/ignored totals, killed-binary detection, cargo
  filters, doctests, and the per-target timing table.
- Buffer per-target output so concurrent failures remain readable.
- Measure serial versus 2-way and, only if safe, 3/4-way wall time on the
  fast lane; reject concurrency that merely creates contention.

## What it assumes from elsewhere

- **[[test-suite-target-timing-and-slow-lane]]** owns target attribution and
  the lane definition. Assumed here: a stable serial baseline and named slow
  targets to use as the experiment.

## Log

- 2026-08-25: Filed after the 2,103-test Squash round measured about ten
  minutes in only 24 visibly slow targets. `cargo nextest` is absent on the
  current toolchain; no unbounded ad-hoc scheduler should replace it blindly.
