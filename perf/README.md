# perf/ — the performance diary

`perf/snapshots/*.json` is what `scripts/perf snapshot` writes: one dated
record per measurement of the suite's per-binary timings, the corpus files
checked cold / warm / edited through the release CLI with `--timings`, and
the phase and per-declaration attribution those tables carry. `scripts/perf
report` reads them as text (deltas against the previous snapshot from the same
environment); `scripts/perf serve` is the dashboard.

Rules, so the diary keeps meaning something:

- **A snapshot is keyed by its environment** (`env.source`: `local` is the
  desktop, `furnace` the cloud box). Seconds are compared only within one
  environment. Counts — conversion queries and misses, evaluator steps — are
  exact on one tree and are the cross-machine line.
- **Attribution runs at kernel width one** (`env.kernel_workers`), where the
  run row's phase columns are honest and comparable with `scripts/test`'s
  width-one target timings; the `wait` mode is one cold check at the default
  width, which is the number a person sits through.
- **Numbers live here and in issue logs, never in docs or CLAUDE.md**
  (`issues/perf-tracking-consistent-environment.md`, 2026-08-12). A doc may say
  "the merkle walk is a sixth of a cold check"; the sixth is a snapshot's.
- **This is a diary, not a gate.** `scripts/bench --check` gates. A snapshot
  is taken when a round wants to know what is slow before choosing, or after
  landing something that should have moved a column; not every round.
- The raw `--timings` tables a snapshot summarized are left under
  `target/perf/<stamp>/` (not committed); `scripts/timings` reads them.
