---
title: Reconcile the saved Nat benchmark timings with the current unchanged kernel
status: open
labels: [kernel,performance,benchmarking]
created: 2026-09-14
updated: 2026-09-14
---

During [[result-propagation]], `scripts/bench --check` flags 12 timing
comparisons after an idle rerun. The task changes no kernel source, kernel
benchmark, Cargo manifest/lockfile, or build configuration. The kernel benchmark
does not depend on syntax or elaboration. Its saved baseline was not rewritten.

The first run overlapped the full suite and reported 20 regressions; discard
that run for interpretation. The isolated rerun reports only these Nat groups:

- step-once at 64/128/256/1024: approximately 1.26–1.28× baseline;
- add-normalize at 64/128/256/1024: approximately 1.25–1.31×;
- mul-normalize at 8/12/32/48: approximately 1.26–1.29×.

The scaling-slope checks do not report failures. Some other families improve,
so this is not evidence for attributing the difference to one uniform host
slowdown. Determine which kernel revision/environment the saved baseline
represents and obtain a controlled comparison before accepting a new baseline
or choosing an optimization. The recorded environment names minus-desktop,
AMD Ryzen 7 5700X, release.

Raw run: `/tmp/result-bench-isolated.log` in the investigation workspace.
Related methodology owner: [[kernel-benchmarks]].
