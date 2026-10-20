---
title: Reconcile the saved Nat benchmark timings with the current unchanged kernel
status: open
labels: [kernel,performance,benchmarking]
area: infrastructure
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

## Log

- 2026-09-14: The isolated post-suite gate for
  [[result-map-receiver-dispatch]] reports six timing flags: `nat/step-once`
  at 64/128/256/512/1024 (1.25–1.29×) and `nat/add-normalize:128` (1.25×).
  No slope failure is reported. This work changes no kernel source,
  benchmark, Cargo manifest/lockfile or build configuration; the kernel
  benchmark does not depend on the modified elaborator. These are further
  observations in the recorded Nat families, not evidence attributing the
  drift to receiver dispatch. Baseline unchanged; raw run
  `/tmp/receiver_bench.log`. The controlled baseline investigation remains open.
- 2026-09-14: The isolated post-suite gate for
  [[callback-expected-type-propagation]] reports seven timing flags:
  `nat/step-once` at 64/128/256/512/1024 (1.26–1.30×),
  `nat/step-into-closed-body:128` (1.25×), and `nat/add-normalize:128`
  (1.26×). No slope failures. This round again changes no kernel source,
  benchmark, Cargo manifest/lockfile or build configuration. The additional
  closed-body flag is recorded without attributing it to the elaborator
  change; controlled baseline comparison remains outstanding. Baseline
  unchanged; raw run `/tmp/callback_bench.log`.
- 2026-09-14: The isolated post-suite gate for
  [[typed-termination-obligations]] reports four timing flags:
  `nat/step-once:256` (1.26×), `nat/step-into-closed-body:128` (1.27×),
  `nat/add-normalize:128` (1.27×), and `nat/mul-normalize:32` (1.26×).
  No slope failures. This round changes no kernel source, benchmark,
  Cargo manifest/lockfile or build configuration. Baseline unchanged;
  raw run `/tmp/typed_bench.log`. These observations do not attribute the
  baseline drift to the elaborator change.
- 2026-09-14: The isolated post-suite gate for [[termination-local-evidence]]
  reports six timing flags: `nat/step-once` at 64, 128, 256, and 1024
  (1.28×, 1.27×, 1.29×, 1.27×), `nat/add-normalize:128` (1.26×), and
  `nat/mul-normalize:12` (1.26×). No slope failures. Kernel sources,
  benchmarks, Cargo configuration and baseline remain unchanged; these
  observations do not attribute the existing baseline drift to this change.
  Raw run: `/tmp/evidence_bench.log`.
