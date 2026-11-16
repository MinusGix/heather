# Cloud benchmarks: the reference environment, and the probe suite

Owning issue: `issues/cloud-benchmarks.md`. The targets the probes were
chosen from, ranked: `perf/bench/targets.md`.

## 1. Cloud timings are the reference

Decided by Minus on 2026-10-29: almost all work now happens in Claude Code
cloud containers, so their timings are the ones that limit a round. Every
benchmark harness records on the cloud box first. Desktop numbers stay useful
as a second opinion, especially as the "lens" ratio the slow-server cadence
was for (`issues/perf-tracking-consistent-environment.md`), but a desktop
baseline is never the one a round is gated against.

What "the cloud box" is: a fresh container from this project's environment,
with its 4 vCPUs and 16 GiB, the toolchain the session-start hook leaves, and
`CLAUDE_CODE_REMOTE=true`. Harnesses record it as environment `source =
cloud`. They compare seconds only when the CPU model, CPU count, build profile
and rustc all match, never on the hostname (the hostname is random per
container: `issues/frontend-bench-baseline-host-string.md`).

The rules from the desktop era still hold, and two of them matter more here:

- **Counters first.** Evaluator steps, conversion queries, substitution and
  rescoping nodes, gated terms: exact for one tree, identical across
  machines. A round that should not change behaviour reads the counters; a
  round that should make something cheaper says which counter fell. Seconds
  confirm a counter, or say what no counter sees (allocation, drops, cache
  misses).
- **Shapes in docs, numbers in results files and issue logs**
  (`issues/perf-tracking-consistent-environment.md`, 2026-08-12). This doc
  carries no timings; `perf/bench/results.tsv`, the baseline TSVs and dated
  issue-log entries do.

Cloud-specific measurement discipline:

- **Nothing else runs.** Four cores and a three-job suite runner leave no
  idle core. A measurement beside `scripts/test`, a `cargo build` or another
  benchmark is not a measurement; the probe harness prints the load average
  and warns above a quarter of the CPU count.
- **Copy the binary first.** Any build relinks `target/debug/heather`, and
  images keyed to the old binary stop matching mid-run. The probe harness
  copies it to `target/bench-probes/heather` before it measures.
- **Width one.** `HEATHER_KERNEL_WORKERS=1`, as the suite runs its children,
  so a row's gate column is that item's and comparable with suite timings.
- **The suite's rails.** 6 GiB of address space per process and a CPU cap,
  so a pathological case dies alone.
- **Cold or warm, say which.** A fresh container has no verdicts and, unless
  the sentinel's images were seeded, no images; a working session has both.
  The same case can differ by an order of magnitude between them, and the
  probes name the state in the case kind.

## 2. The five harnesses, and what each one is for

| harness | question | records in |
|---|---|---|
| `scripts/bench` | the kernel's cost model: exponents of reduction, substitution, conversion | `crates/kernel/benches/baseline.tsv` |
| `scripts/bench-frontend` | the wait for one file: latency and phase split of elaboration | `crates/elab/benches/baseline.tsv` |
| `scripts/bench-probes` | where the real library and the native compiler spend: one slow declaration or one fixed cost at a time, through the CLI the suite runs | `perf/bench/results.tsv` |
| `scripts/bench-native` | the code the compiler emits: the linked SHA-256 and scanner against Rust references, instructions per block, compile time (`docs/native/native-benchmarking.md`) | `crates/linked/benches/baseline.tsv` |
| `scripts/perf snapshot` / `ab` | the diary of whole files and the suite; whether one change made a file faster | `perf/snapshots/*.json` (`env.source = cloud`) |

The first two run in-process over closures they build from source, which
keeps them self-contained but cannot reach what is slow in native work: the
image store, the merkle walk, `write-elf`'s certificate, or a declaration
whose prefix is most of the library. The probes exist for those.

## 3. The probe suite

```
scripts/bench-probes                       # every default case, three samples, printed
scripts/bench-probes --filter native       # the cases whose name contains it
scripts/bench-probes --heavy               # also the cold write-elf cases
scripts/bench-probes --check               # against perf/bench/results.tsv; exit 1 on a regression, 3 if shape-only
scripts/bench-probes --save                # record (a filtered --save replaces only its own cases)
scripts/bench-probes --list
```

`perf/bench/cases.tsv` lists the cases. Each names a file, a target and a
kind:

- **`only`**: `heather check --cache --only ITEM FILE`. `--only` elaborates
  and kernel-checks exactly the named items over a replayed prefix and never
  publishes or writes a verdict (`docs/infrastructure/check-only-design.md` §2), so a sample
  repeats exactly and leaves the store as it found it. The row is the
  item's own: its marginal cost with everything before it replayed. The
  process around it is mostly the replayed world, which is a case of its own
  (`native/world-replay`); an `only` case is gated on the item's seconds, not
  the process's.
- **`warm`**: `heather check --cache FILE` after two unmeasured runs, so every
  module is an image hit and the run row is what loading the world costs.
  Two, because a module the store had no image for is elaborated by the
  first and replayed for the first time by the second, which is when its
  statements' verdicts are recorded.
- **`elf-warm`**: `heather write-elf` after two unmeasured runs, so the
  certificate's verdicts are stored. What is left is the fixed cost every
  `write-elf` pays with no kernel work.
- **`elf-cold`** (with `--heavy`): `write-elf` over a fresh copy of the store
  for every sample, so the certificate is checked cold, as the native gates
  check it on a fresh box.
- **`cert`**: `only` over the certificate `write-elf FILE SYMBOL` writes
  today, on the items whose names match a glob (target `SYMBOL:GLOB`, such
  as `yes_tool:yes_tool_elf_piece_*_is`). The write-elf is unmeasured, runs
  once per symbol, and leaves its certificate under
  `target/bench-probes/out/certificates/` as `SYMBOL_elf_certificate.hthr`
  (a module is named by its file stem, so write-elf's `.certificate.hthr`
  name is copied to one that is an identifier).

Before measuring, the harness warms `target/bench-probes/store` with one
`heather check --cache --world lib --expectations` per library folder a case
reads, in the library gate's order. On a working box that is a replay of
images the suite already built. On a fresh box, or after a compiler edit, it
is the gate's cold build of those folders. It is never timed. No case writes
to that store: the `elf-*` cases copy it (so the certificate stays cold), and
the others run over a copy taken at the start, because priming a fixture
publishes verdicts, and a `cert` case's write-elf publishes the
certificate's, which the `elf-*` cases must check cold.

A certificate case reads the certificate the current compiler writes, not a
frozen copy. A frozen copy kept the workload fixed while the checker
changed, but it stopped checking once the library renamed what it cited
(`issues/bench-probe-cases-stale-2026-11.md`). The price is that a change to
what `write-elf` emits moves the `cert/*` counters too: when a round changes
the emitter, its moved `cert/*` counters are partly the new certificate, and
the item names in the case's glob must still match it.

### Reading a row

`time` is the headline (the item rows' total for `only`, the process's CPU
for the other kinds). Then `cpu`, and the row's self time split four ways:
`kernel` (the gate), `merkle` (the cache's interface and check-key walks),
`image` (decode, recheck, relocation, publication, hashing) and `elab` (the
rest). Then the spread of `time` across samples and the counters. The
counters are exact, with two exceptions: `local_subst_nodes` and
`shift_global_nodes` move by a small fraction between identical runs,
because the memos that save that work are keyed by node address. They are
compared within 5%. Any other counter that differs between samples is
printed as unstable, which means the case has stopped being deterministic,
and that is a bug in the case.

`--check` reports every counter that moved against the recorded row, and
fails when `time` is at least 1.25× the recorded value on the same
environment key. A moved counter is not a failure: when a round meant to move
it, the moved counter is the round's result, and `--save` records it.

### What a cold gate's per-item column means

A cold library gate charges a generated item the module shares (a generated
definition, an instance, an omega lemma) to the first declaration that needs
it. That declaration's cold gate time can be many times its `only` time,
where the shared items are already vouched for. Both are true: the cold row
is what the module pays, and the `only` row is what that declaration adds.
Rank targets by the cold module totals and measure them by `only`.

### Adding a case

Add a row to `perf/bench/cases.tsv`, with a `why` that says what the case
isolates. Then add its target's entry to `perf/bench/targets.md`, run it with
`--filter` until its counters are stable across samples, and `--save`.
Prefer an `only` case over a whole process. Prefer a library declaration
that a round will actually change over a fixture copy. A fixture is for
generated text and for fixed costs that need a root of their own.

## 4. Hillclimbing on a case

1. Pick a target from `perf/bench/targets.md` (cost, owner issue, case).
2. `scripts/bench-probes --filter <case> --check` before touching anything,
   so the recorded row is known to reproduce on this box.
3. Iterate with `--samples 1`, reading counters, which are exact at one
   sample. Do not read a one-sample time: right after a warm step that
   rebuilt images, one sample has read past the 1.25× threshold with every
   counter unchanged, and three samples on a quiet box matched the row.
4. Finish with three samples, `--check` over every default case (the
   neighbours are the regression check), and `--save`. Say in the commit
   which counter moved and by how much.
5. For a whole-file claim, `scripts/perf ab` is still the instrument
   (`perf/README.md`); the probes say where, `ab` says whether.
