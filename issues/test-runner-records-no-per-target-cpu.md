---
title: The test runner records wall time, so a target drifting toward the CPU rail is invisible until it SIGKILLs
status: closed
labels: [testing,tooling,robustness]
created: 2026-09-17
updated: 2026-09-17
---

`scripts/run-test-targets.mjs` kills a child that exceeds `ulimit -t 300` — a
**CPU-time** rail — and records, per target, only **wall** time
(`target/test-target-timings-<lane>.tsv`, and the `slowest test targets` table).
Those are different quantities, and for a multi-threaded child they are not
even proportional: the same target measured alone on an idle box was 43.7 s
wall / 274.5 CPU-s at the gate's default width and 110.0 s wall / 109.4 CPU-s
serial — the *slower* configuration by wall clock is the one with 2.5x the
headroom against the rail.

So nothing in the suite's output says how close any target is to the limit it
is killed by. A target drifting toward it is invisible until the day it crosses,
and then it surfaces as `INCOMPLETE` plus one `[target exit: code=none,
signal=SIGKILL, result-lines=0]` line buried above 200 targets' output — with no
history to say whether it was always marginal or doubled last week.

That is how [[native-summary-test-cpu-margin]] was found: by hand, after the
fact, by re-running one target under the runner's own invocation with `time`.

## What it would take

The runner spawns each child itself, so the numbers are there for the asking:
`child.on("close")` can carry the child's `rusage` (or the wrapper can `time`
it), and the TSV already has a per-run, per-target row to put it in. Then the
summary can say which targets are within some fraction of the rail, the way
`scripts/bench --check` says which families regressed.

## Acceptance

- The per-target TSV records CPU (user + sys) alongside wall time.
- A target above some fraction of the CPU rail is *named* in the run's output
  while it still passes — a warning, not a kill.
- The threshold and the warning are cheap enough to leave on for every run;
  this is a rail, not a benchmark, so nothing here needs a quiet box.
- The append-only history keeps the CPU column, so drift is diffable across
  runs the way the wall column already is.

## What it assumes from elsewhere

- **[[native-summary-test-cpu-margin]]** owns the rail and the targets that sit
  near it. Assumed here: only that the rail is CPU time and that crossing it is
  a `SIGKILL` with no surviving `test result:` line.
- **[[scripts-test-killed-binary-reads-green]]** owns the summary line that
  already refuses to print a green count when a binary dies. Assumed here: only
  that it reports the death after the fact; this issue is about seeing it
  coming.

## Log

- 2026-09-17: Filed while fixing the suite's inability to go green
  ([[native-summary-test-cpu-margin]]). The fix there removed the contention
  that was consuming the rail; this is the instrument that would have shown it
  without a hand measurement, and that would show the next one.
- 2026-09-17: Done. scripts/run-test-targets.mjs no longer exec's the child from its ulimit wrapper: bash stays the parent, `time "$@"` with a TIMEFORMAT marker prints user+sys (every thread — the quantity `ulimit -t` kills on) and the wrapper re-raises the child's signal so a rail kill still reads `signal=SIGKILL`. parseCpu strips the marker from the output, the `[done]` line and the slowest-targets table print CPU-s and the percentage of the 300 s rail, any target past 50% of the rail is listed under its own heading every run, and the timings TSV gains a fourth column (older rows still read; scripts/perf's suite reader and the dashboard carry it). Covered by scripts/test-target-runner.test.mjs, including an end-to-end wrapper case for exit code, CPU line and signal re-raise.
