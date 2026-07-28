---
title: Benchmark suite for the frontend (parse, elaborate, full-file check)
status: open
labels: [frontend,elaboration,performance,tooling]
created: 2026-07-27
updated: 2026-07-27
---

Companion to [[kernel-benchmarks]], separate because the questions differ:
the kernel's cost model must stay simple and predictable; the elaborator is
*allowed* to be clever, so what its benchmarks guard is user-facing latency —
time from source file to checked declarations — and how it scales with file
size, meta count, and generated-term volume.

## What this issue owns

Designing the frontend benchmark suite: harness, fixtures, and the latency
budget worth alarming on. Not any particular speedup.

## Design questions

- **Fixtures.** The stress-proof suite files are the natural corpus — real
  proofs, already maintained, already exercising the unifier, the inductive
  compiler and the container schemas. Plus a generated-scale fixture (many
  declarations, wide inductives) so growth is measured, not just the suite's
  current size.
- **What to time.** End-to-end per file, but also split parse / elaborate /
  kernel-check, so a regression names its layer. The kernel-check split
  overlaps [[kernel-benchmarks]] deliberately — same number, different
  question (there: cost model; here: how much of user latency it is).
- **Where it runs.** Wants [[cli-check-diagnostics]]: once a file can be
  checked from the CLI, "time the CLI on the corpus" is the whole harness,
  which is one more reason that issue is scheduled first.
- **Unifier pathology.** [[elab-unifier-completeness]] owns postponement;
  assumed here only that meta-heavy files exist to measure. A fixture that
  provokes retry/postponement behavior keeps quadratic blowups visible.

## Log
