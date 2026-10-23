---
title: The heavy corpus cases make every later family in the same run read 1.3-1.5x slow, so the time half of --check cannot gate at 1.25x
status: closed
labels: [frontend,tooling,performance]
created: 2026-08-17
updated: 2026-09-11
---

## Log

- 2026-08-17: FOUND by controlled experiment, 2026-08-17 (managed tooling round; measured on minus-desktop, release, desktop-only load 2.0). The absolute-time half of scripts/bench-frontend --check disagrees with itself by more than its own 1.25x threshold, and the variable is not the machine's load -- it is WHAT ELSE RAN IN THE SAME PROCESS.

Same code, same baseline (re-recorded that day from a full run), four measurements within about twenty minutes:
- full --check, three consecutive runs: scale/declarations:32/64/128 at 1.28-1.34x / 1.28-1.58x / 1.38-1.57x over the baseline row, scale/wide-inductive:8 at 1.29-1.41x, and in one run three forded/declared-index-tags cases at 1.26-1.27x. 4, 7 and 4 flags.
- `--check --filter scale/declarations` (that family alone): ok, 5 comparisons within thresholds.
- --check --no-heavy (everything except the three ir_v1 corpus cases): OK, 50 comparisons within thresholds, in the same minute as a red full run.
- and two earlier full runs the same evening (the --check before the re-record and the --save itself) read the cheap families FAST, matching --no-heavy.

So a family reads 1.3-1.5x higher when the heavy `lib/certgen/ir_v1.hthr` corpus cases have run before it in the same process, and whether it does appears to depend on the machine's memory state at the time: this machine had 800 MB free with 37 GB in page cache and 10.5 GB of swap in use, and the ir_v1 closure allocates on the order of 100 MB per round (peak RSS ~106 MiB for the run). Reclaim/fragmentation is the obvious suspect; nothing here proves which.

Why it matters: --check's threshold for 'a case is slower' is 1.25x, i.e. BELOW the contamination. So on a full run the time half produces flags that no round can act on, which is exactly the failure [[frontend-benchmarks]]'s bands were just fixed for. Note this was invisible until 2026-08-17 for an unrelated reason -- [[frontend-bench-baseline-host-string]]: the recorded baseline's host string did not match this machine, so the time half was not being compared at all.

Candidate fixes, in the order this round would rank them, none implemented (out of that round's scope):
1. Measure the heavy cases LAST, whatever order they are reported in -- their own numbers are seconds-scale and insensitive to allocator state, and the cheap families then get a clean process. Cheapest, but it does not touch the intermittency, only the ordering.
2. Give the corpus family its own process (the harness already forks a worker; a second one for heavy cases is a small step) -- this is the only option that actually isolates a 100 MB workload.
3. Normalize each run by a per-run machine factor (median ratio across comparable cases) and gate on the normalized ratio. Cheap and it would have made all four of the above runs agree -- but it makes a GLOBAL regression invisible by construction, which is a real loss and wants a deliberate decision.
4. Raise time_regress above the measured contamination. Masks the signal; recorded only so the list is honest.

Interim protocol, written into docs/frontend-benchmarking.md: for the time half, believe --no-heavy; run the full suite for the slope bands, the latency budgets and the guards, which are unaffected (all three were green in every run above).

## What it assumes from elsewhere

- **[[frontend-benchmarks]]** owns the suite, its thresholds and its baseline.
  Assumed here: only that `--check`'s time comparison fails a case at 1.25x.
- 2026-08-17: 2026-08-17: the same signature turned up on the KERNEL harness, filed as [[kernel-bench-full-run-flags-drift]]: four consecutive full 'scripts/bench --check' runs on one unchanged binary flagged nine distinct fixtures between them, none in all four, all in the 1.25-1.5x band, while every filtered re-run of a flagged family was green and every scaling exponent stayed in band. Bearing on this issue: candidate fixes 1-3 are now wanted twice, or the two harnesses have to stop being siblings. Nothing here re-measures the frontend claim; it is cross-linked so that whoever takes one takes the other knowingly.
- 2026-09-11: Merged into [[perf-tracking-consistent-environment]] 2026-09-11: same signature as the kernel bench drift, one decision (instruction counts, not wall-clock, as the gate). --no-heavy remains the interim protocol. Closing.
