---
title: Record benchmark timings on the cloud box, and keep a probe suite of the slow native costs
status: closed
labels: [performance,benchmarking,tooling,native]
area: infrastructure
milestone: [hih-tools]
created: 2026-10-29
updated: 2026-10-29
---

Minus, 2026-10-29: almost all work now runs in Claude Code cloud
containers, so local timings are not what limits a round. Record benchmark
times on the cloud box, find which files and declarations are slow and where
their cost comes from (elaboration, kernel, certificate), turn the top costs
into small benchmarks, and hillclimb on them. Native code first. Do not run
the full suite to find out.

## What this issue owns

- The convention: cloud timings are the reference, how they are taken, and
  how the four harnesses relate (`docs/cloud-benchmarks.md`).
- The probe suite: `scripts/bench-probes`, `perf/bench/cases.tsv`, its
  fixtures, and `perf/bench/results.tsv`.
- The ranked target list, `perf/bench/targets.md`. Each target names the
  issue that owns the work on it. This issue owns none of that work.

## What it assumes from elsewhere

- **[[perf-tracking-consistent-environment]]** owns where trustworthy
  numbers come from. Assumed here: only its rule that numbers live in results
  files and issue logs, not docs.
- **[[frontend-benchmarks]]** and **[[kernel-benchmarks]]** own their
  suites. Assumed here: only that their baselines move to the cloud box when
  next recorded (both were recorded on the desktop).

## Done when

The probe suite has a cloud row for every case, the target list has an
owner for each target, and the kernel and frontend baselines have been
re-recorded on the cloud box.

## Log

- 2026-10-29: Built (branch claude/project-thread-fod7fz). Attribution
  without the full suite: a cold library gate run by hand one folder at a
  time with `--timings` (the gate's command, 3 at a time, width one), every
  native tool's `write-elf` over a fresh copy of that store (a cold
  certificate), `--only` on the top items, and a warm second `write-elf`.
  The findings and their numbers are in `perf/bench/targets.md`. New issues
  for what had no owner: [[native-process-fixed-cost]],
  [[native-gate-child-cold-at-rail]], [[native-lemma-kernel-steps]].
- 2026-10-29: The kernel and frontend baselines were re-recorded on the cloud
  box (`scripts/bench --save`, `scripts/bench-frontend --save`, full runs,
  nothing else running). Six declared bands are left by the cloud slopes,
  and [[cloud-bench-bands-out-of-range]] owns them. Every "done when" item
  is met, so this closes; the targets' work is owned by the issues
  `perf/bench/targets.md` names.
