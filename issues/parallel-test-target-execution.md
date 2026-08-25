---
title: Run independent test binaries in bounded parallel under suite limits
status: closed
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
- 2026-08-25: Landed a first-party scheduler for unfiltered full and fast
  workspace runs. Cargo still compiles and discovers all targets; 138 libtest
  executables then run two at a time by default, with complete output buffered
  per target, and Cargo retains the serial doctest phase. Each child inherits
  the existing 4 GiB address-space, 300 CPU-second, 8 MiB stack, and two-test-
  thread rails. The requested worker count (`HEATHER_TEST_JOBS`, default 2) is
  additionally capped by `/proc/meminfo`: four GiB per possible child plus a
  two GiB host reserve; unreadable memory information degrades to one worker.
  The timing-sensitive frontend benchmark smoke is exclusive. Focused Cargo
  invocations retain the old serial runner, avoiding a second implementation
  of Cargo's selection syntax.

  First clean `scripts/test --fast` measurement: 2,024 passed plus all five
  doctest targets, 349.87 seconds of reported target work in 179 seconds of
  runner wall time, a 1.95x compression (the sequential-work sum is the exact
  same-run serial lower bound, chosen instead of spending another six minutes
  on a redundant one-worker run). The first run was alphabetical; later runs
  persist target timings under `target/` and schedule longest-first. A focused
  serial Squash run also remained green. Artifact/result/memory-bound policy
  has dependency-free Node regression coverage invoked by `scripts/test`.
  Final full-lane verification: 2,103 passed plus all five doctest targets,
  594.15 seconds of reported target work in 300 seconds of test-runner wall
  time (301 seconds including inventory and runner checks). This exercises the
  slow acceptance lane and confirms the same near-ideal two-way compression.
