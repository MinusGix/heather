# Measuring performance

Perf measurement is not part of an ordinary round (the root `CLAUDE.md` says
when it is). These are the tools for a round that does measure.

- **Benchmarks: `scripts/bench`** (same `ulimit` discipline; never bare
  `cargo bench`). `--check` gates against `crates/kernel/benches/baseline.tsv`;
  the headline number is the scaling exponent, not the time.
  `docs/benchmarking.md` explains "regressed" and why the harness is
  first-party (the kernel has zero dependencies, dev-dependencies included).
- **Cloud timings are the reference**: record and compare
  on the cloud box, counters first (`docs/cloud-benchmarks.md`). To
  hillclimb on a slow native or library cost, use **`scripts/bench-probes`**:
  one declaration or one fixed cost per case, from `perf/bench/cases.tsv`,
  chosen from the ranked `perf/bench/targets.md`.
- **What is slow right now: `scripts/perf report`** (`perf/README.md`), over
  the environment-keyed diary in `perf/snapshots/` (`snapshot` records,
  `serve` is the dashboard). Read it before choosing a perf target, so a round
  attacks what the corpus says dominates, not the item in front of it. A
  diary, not a gate.
- **Did a change make it faster: `scripts/perf ab`** (`perf/README.md`). Never
  hand-roll a before/after pair — hand-rolled pairs have given confident wrong
  answers. It builds both binaries, interleaves cold samples, and reports
  **counters and seconds apart**: a moved counter is a behaviour change; a
  seconds delta inside the per-sample spread is no result. The README has the
  flags; the two that are easy to get wrong:
  - With `--patch` (a checkout with no `.git`), `--touch` is mandatory or
    cargo returns the stale binary.
  - **`lib/` or showcase changes** use `--source-patch FILE`, which holds the
    binary fixed; a moved counter is then the round's result, not an alarm.
- **Read a `--timings` TSV with `scripts/timings`**, never by counting
  `awk -F'\t'` indices. It looks columns up by name (`--diff a.tsv b.tsv` for
  per-item deltas; identical count columns prove a refactor changed no terms),
  and its help defines `queries`. Counts are exact and worker-count-invariant;
  seconds are not, and at width > 1 item times sum past the run row.
- **Item timings compare only at the same kernel-gate width**
  (`HEATHER_KERNEL_WORKERS`, `--kernel-workers`; eight by default, and
  `scripts/test` runs its children at width one).
