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
- **One corpus entry is a certificate, not a check**:
  `examples/x86-native/program.hthr` runs through `compile-x86 program`
  (`COMPILE_X86` in `scripts/perf`), the x86 line's recipe, so the generated
  certificate's items are in the report beside the library's. Snapshots
  before burn B2 have `reused_callee.hthr` through `build-x86` in that place,
  the per-function certificate; the two rows are different workloads.

## Exploring one run: the dashboard's Explore section

`scripts/perf serve` (or the `perf` entry of `.claude/launch.json`) also
serves each snapshot's raw `--timings` tables while they are on disk, found
under any worktree of the repository. Explore reads them: a treemap of one
file's run, module → family → declaration (a family is a generated name with
its numeric segments as `#`, so `caller_native_read_literal_28_3` is one of
`caller_native_read_literal_#_#`), sized by any column and colored by the
phase that dominates; the groups at the current level with a stacked phase
bar each; and every declaration under it, sortable and filterable, with Δ
columns when the compared snapshot's table is on disk too. Every `*_ns`
column is self time and they sum to `total_ns`, so a bar is the whole row.

## Inside the suite: per test, and per declaration

The suite section is not only one number per test binary. The runner records
**seconds per test** on every run (libtest `--report-time`, in
`target/test-times-<lane>.tsv`; `HEATHER_TEST_TIMES=0` turns it off), and a
snapshot keeps every test at or above 50 ms: the dashboard's *Inside the test
binaries* treemap and table.

One level further down is opt-in: `HEATHER_SUITE_DECLS=1 scripts/test --fast`
makes every test thread write its `--timings` rows (`HEATHER_TIMINGS_DIR`,
`crates/elab/src/stats.rs`) to `target/suite-decls-<lane>/`, and the next
snapshot sums them across the suite — *What the suite elaborates*: modules and
declarations summed over the tests that elaborate them (a library module
re-elaborated from source by a hundred tests is one row), and each test's time
inside declarations against its time outside any (image replay, generators,
the test's own work).

## What the report shows besides totals

Every heaviest-declaration row carries the gate's **µs per evaluator step**
and the **rescope** count (`shift_global_nodes`: nodes the kernel walked
rescoping definition bodies and global references into the ambient Ψ), and
a **per-step outliers** section lists the items whose gate costs at least
ten times the file's median per step. A table sorted by total hides that
family: few steps, few queries, and seconds in what each step touches
(`issues/refl-theorem-step-cost.md`, where fourteen refl theorems were
invisible at 0.5–1 s each). The snapshot keeps the file's per-step median and
its own outlier list (`items.outliers`), so the section does not depend on an
item also being among the heaviest by total.

## Is this change faster? `scripts/perf ab`

A snapshot answers *what is slow*. Whether one change made it faster is a
different measurement, and it is the one that keeps going wrong by hand:

    scripts/perf ab --marker global_sig_rescopes            # HEAD vs this working tree
    scripts/perf ab --base HEAD~1 --samples 5               # the last commit against its parent
    scripts/perf ab --patch round.patch --touch             # on a box without git (furnace)
    scripts/perf ab --replay                                # re-render the last report, measuring nothing
    scripts/perf ab --source-patch showcase.patch           # a change to lib/ or a showcase: one binary, two source trees
    scripts/perf ab --base REV --whole-tree --file F        # compiler and lib/ changed together: each binary over its own tree

It builds both binaries, parks a copy of each (a `cargo build` writes one
path, and an A/B builds twice), interleaves `--samples` cold checks of each,
and reports counters and seconds **separately**. The `before` tree is a reused
git worktree at `--base`, keyed by commit so its cold build is paid once — or,
with `--patch`, this tree with a diff reversed and restored afterwards, which
is what a furnace checkout needs because it has no `.git`
(a furnace checkout is a plain copy of the working tree).

What it refuses to let you get wrong, each because it happened:

- **Which binary is which.** The two are hashed and an identical pair is a
  hard error: `cargo build` will hand back the artifact it already has when it
  judges a tree fresh, which on furnace it does routinely — the checkout is an
  rsync of the working tree, so source mtimes are the *local* ones while
  `target/` lives on a volume that outlives instances. `--touch` defeats that;
  pass it there always. `--marker COLUMN` is the strongest check available when
  a round adds a counter: the after binary must emit that `--timings` column
  and the before binary must not.
- **Counters and seconds are different claims.** Counters are exact on one
  tree and equal across machines; the report lists every column that moved and
  says how many did not. A round whose verdicts should not change reads that
  list, not the clock. Seconds are environment-local and get the per-sample
  spread printed beside the median, with the verdict `separate` only when the
  two sample sets are disjoint — otherwise `SPREAD EXCEEDS THE DELTA — not a
  result`.
- **A loaded box.** Load average is printed and warned about above a quarter of
  the CPU count. A desktop under a game once read a −8.9 % gate win as −2.9 %
  and invented a +35 % per-item regression that a quiet box puts at −1.3 %
  (`issues/signature-rescope-multiplicity.md`).
- **Items that are not really there.** The per-item table ranks only items every
  sample on both sides reported, and only above a 5 ms floor: a snapshot keeps
  the heaviest N items plus the per-step outliers, so an item near that cut
  drifts in and out between samples and its "delta" is the cut moving. What was
  dropped, and why, is printed.

### A round that changed both: `--whole-tree`

When a round changes the compiler and `lib/` together, neither mode above
applies. The before binary cannot check the after tree's library, because it
emits constructors the library no longer has, and the after binary cannot
check the before tree's. `--whole-tree` (with `--base`) runs the before binary
inside its worktree, over that commit's sources. Each side is then one whole
tree, and a moved counter is the round's combined result. The native build
workload (`COMPILE_X86`, `examples/x86-native/program.hthr`) is the usual
reason to use it.

### A source change: `--source-patch`

A change to `lib/` or to a showcase is the same measurement pointed the other
way — **one binary over two source trees**, where the binary A/B is two
binaries over one. Without this, `ab` builds the same binary twice, finds the
hashes equal and refuses the run, correctly by its own rules
(`issues/perf-ab-source-patch.md`).

    scripts/perf ab --source-patch round.patch --samples 3
    scripts/perf ab --source-patch round.patch --heather target/release/heather   # skip the build
    scripts/perf ab --source-patch round.patch --file docs/showcase/calc_text.hthr:lib/std,lib/std/parser

Everything above still holds — the interleaving, the spread verdict, the
loadavg warning, the item filters, the replay. Four things differ:

- **The provenance assertion is inverted.** The binary is *supposed* to be
  identical on both sides; it is the two source trees that must differ. So the
  refusals are the mirror image: a patch that names no files, a patch whose
  reversal leaves every file byte-identical, and — the one worth knowing — a
  patch that touches `crates/` or `Cargo.*`, which breaks the premise that the
  binary is fixed. That last case is what plain `--patch` is for.
- **A moved counter is the result, not an alarm.** In binary mode a counter
  that moved means the round changed behaviour it did not mean to. For a source
  change, term growth is exactly what is being traded for readability, so the
  moved columns are the finding and are ranked by how far they moved.
- **The corpus defaults to the files the patch touched**, where any of them is
  in the corpus, because measuring the default showcase would be measuring
  something else. Where none is — the change reaches the corpus only through an
  import — the report says so, so that "no change" is not read as a finding.
  `docs/showcase/calc_text.hthr` is **not** in the corpus (its own
  `parser_core` clashes with the library's on a shared `-L` path), so name it
  with `--file`.
- **`--marker` is refused**: it asserts a column the *after binary* adds, and
  there is only one binary here.

A last thing this mode does not decide: whether the change is worth making. A
readability round is not a perf round — if the nicer spelling costs, that is a
finding about the language or the kernel to file, not a veto on the edit
(`issues/showcase-spec-relations-as-records.md`). This measures; it does not
gate.

The raw tables are left under `target/perf-ab/raw/` and the whole report is
replayable from `target/perf-ab/last.json`, so re-reading an A/B costs nothing.

`scripts/perf ab-selftest` asserts the report's pure logic — the spread verdicts,
the two filters above (each of which this report shipped without for an
afternoon), and that the two modes read a moved counter differently. It is not in `scripts/test`: there is no python test lane here (the one
tested script is the node runner, `scripts/test-target-runner.test.mjs`). Run it
by hand after touching `report_ab`.

## Probing one declaration

`heather check --cache --only <item>[,<item>…] --timings f.tsv <file>`
elaborates and kernel-checks exactly the named declarations (`name` in the
root module, `module::name` anywhere in the closure) over a prefix replayed
from the store, publishes nothing, and labels the run row `only=…` so that
`scripts/timings` says so and refuses to diff it against a whole run. Counts
reproduce a whole run's to the unit or nearly (see
`docs/check-only-design.md` §4 for the one measured exception); times are a
series of their own. The store must hold an image of the module first:
`heather check --cache <file>` once.
