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
  hillclimb on a slow native or library cost, use **`scripts/bench-probes`**
  (`--filter`, `--check`, `--save`; `--heavy` adds cold `write-elf`s): one
  declaration (`--only`) or one fixed cost per case, from
  `perf/bench/cases.tsv`, chosen from the ranked `perf/bench/targets.md`.
- **What is slow right now: `scripts/perf report`** (`perf/README.md`), over
  the environment-keyed diary in `perf/snapshots/` (`snapshot` records,
  `serve` is the dashboard). Read it before choosing a perf target, so a round
  attacks what the corpus says dominates, not the item in front of it. A
  diary, not a gate.
- **Did a change make it faster: `scripts/perf ab`** (`perf/README.md`). Never
  hand-roll a before/after pair — hand-rolled pairs have given confident wrong
  answers. It builds both binaries, interleaves cold samples, and reports
  **counters and seconds apart**: a moved counter is a behaviour change; a
  seconds delta inside the per-sample spread is no result.
  - `--base REV` builds the before side in a reused git worktree; `--patch
    FILE` reverses a diff in this tree (for a checkout with no `.git`), and
    there `--touch` is mandatory or cargo returns the stale binary.
  - `--marker COLUMN` asserts the after binary emits a new counter;
    `--replay` re-renders the last report.
  - **`lib/` or showcase changes**: `--source-patch FILE` holds the binary
    fixed and reverses the diff over the sources (`--heather BIN` skips the
    build); a moved counter is the round's result, not an alarm. It refuses a
    patch touching `crates/`.
- **Read a `--timings` TSV with `scripts/timings`**, never by counting
  `awk -F'\t'` indices. It looks columns up by name (`--diff a.tsv b.tsv` for
  per-item deltas; identical count columns prove a refactor changed no terms).
  `queries` = shortcut + memo + miss over `Tc::conv_ty`; attribution docs
  written before it quote `conv_shortcut_hits` alone, so reproduce theirs with
  `--columns shortcut`. Counts are exact and worker-count-invariant; seconds
  are not, and at width > 1 item times sum past the run row.
- **Item timings compare only at the same kernel-gate width**
  (`HEATHER_KERNEL_WORKERS`, `--kernel-workers`; eight by default, and
  `scripts/test` runs its children at width one).
