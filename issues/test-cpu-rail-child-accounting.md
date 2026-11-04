---
title: Distinguish aggregate child CPU from per-process test rails
status: open
labels: [tests,tooling]
area: infrastructure
created: 2026-09-20
updated: 2026-11-04
---

## Scope

`scripts/run-test-targets.mjs` wraps each test target in Bash `time`, reporting
user+system CPU as a percentage of the 300-second `ulimit -t` rail. For targets
that spawn and wait for children, the reported CPU includes descendant work;
the resource limit applies independently to each process. A target can therefore
finish successfully with aggregate reported CPU above 300 seconds.

The isolated composed-summary fixtures in
[[x86-composed-summary-test-cpu-margin]] make this visible: the CLI test target
reports 317.4 CPU-s while each process retains the unchanged 300-second limit.
The resource separation is intentional; the displayed percentage is misleading
as a statement about the root process's remaining allowance.

## Acceptance

- Label aggregate timing explicitly, and avoid treating its ratio to one
  process's rail as a precise headroom measurement.
- If per-process headroom is reported, collect actual process-level CPU rather
  than subtracting guessed descendant costs.
- Preserve all current CPU/memory limits, scheduling, signal propagation, and
  test-result counting.
- Cover a bounded test that spawns a child, alongside a single-process target.

## Log

**2026-11-04.** This blind spot is why the 2026-11-03 and 2026-11-04 master
reds had no warning: native_tools reports 2932 CPU-s as a target, always far
"past" a 300 s rail it is never killed by as a whole, while its one
`write-elf` child per test sits at 100% of its own rail
([[native-sort-gate-rail]], [[master-red-2026-11-04]]). The library gate's
heaviest module children sit at 40–50%.
