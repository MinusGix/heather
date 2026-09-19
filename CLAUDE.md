# Heather — working notes for Claude

- **Run tests only via `scripts/test`** (wraps `cargo test` in `ulimit -v/-t`
  plus a thread cap). Never run bare `cargo test`: a runaway test or a
  Debug-formatted kernel term can OOM the whole machine, not just the process.
  `scripts/test --fast` (about a minute of tests on a warm furnace box, plus
  whatever needs recompiling; what it skips and what
  dominates what remains live in `issues/certgen-harness-cost.md`) skips the
  whole-library acceptance tests, the perturbed-library mutation controls
  (~4.7 CPU-min), and the native x86 certificate gates
  (`crates/cli/tests/native*.rs` plus their warmup, ~20 CPU-min;
  `issues/native-summary-test-cpu-margin.md`) for the inner loop, and replays semantic test images that
  an earlier build of the compiler wrote (vouched for by the verdict store
  at `target/decl-cache` or kernel-rechecked, but the current frontend is
  not re-run on unchanged library modules); a round's **final**
  verification, and any change touching `lib/`, the kit, or the generators,
  must run the plain full `scripts/test`, which rebuilds such images.
  `scripts/test --long` (own target dir) additionally runs every slow kernel
  self-check on every occasion (`crates/kernel/src/checks.rs`; the default
  samples one in sixteen) — a sweep for rounds that touch the kernel's
  traversals or bounds memo, not a gate. The suite ends with one `== suite: N passed, … ==`
  line — read that instead of re-running to grep failures and sum counts
  separately; if it says `INCOMPLETE`, a test binary died (usually the
  ulimit) and the counts are partial, not a smaller green suite. Run the full suite **in the background** and do doc/bookkeeping
  work while it runs; don't sleep-poll it.
- **Perf measurement is not part of an ordinary round.** Elaborator changes —
  even complex ones, as long as they add no inference route on a hot path —
  land without timing anything; `scripts/bench --check` against the baseline
  is what catches regressions. Only a round whose issue names performance as
  the point measures, and then through `scripts/perf ab`, never by hand.
- **The same goes for direct `heather` runs**: deep conversion workloads are
  memory-superlinear (an uncapped release `heather check` on a deep-fuel IR
  theorem hit ~22 GB, 2026-07-31). Wrap every invocation:
  `(ulimit -v 8388608 -t 120; target/release/heather check <file>)`,
  loosening deliberately per run if needed — never uncapped. **To probe one
  declaration**, `--cache --only <item> --timings f.tsv` elaborates and gates
  just it over a replayed prefix (13 s instead of 48 s on the showcase's
  heaviest item; `docs/check-only-design.md` — the run is labelled and
  `scripts/timings` refuses to diff it against a whole run). After editing
  the compiler's Rust, `--cache --accept-stale-images` replays the library's
  module images instead of re-elaborating them (same trade as the fast
  lane; drop the flag for a final check).
- **The kernel gate runs eight workers by default** (`HEATHER_KERNEL_WORKERS`,
  `--kernel-workers`); a proof's item timing is only comparable across runs
  at the same width, and `HEATHER_KERNEL_WORKERS=1` is the serial build for
  isolating one item. The suite's per-process address-space rail is 6 GiB.
  **`scripts/test` runs its children at width one** since 2026-09-17: the
  runner already schedules targets in parallel and budgets two CPUs each, so
  eight workers underneath that multiplied the box's load ~8x and the CPU rail
  (`ulimit -t 300`, which counts every worker thread) was measuring contention
  rather than test cost — one target reached 274 CPU-s against 300 for 109 CPU-s
  of work, and no full run could go green. Width one made the suite green *and*
  faster. So timings read out of a suite run are width-one timings; set
  `HEATHER_KERNEL_WORKERS` explicitly to override, which still wins.
- **Builds link with mold** (`.cargo/config.toml`), which reserves ~8 GiB of
  address space per link, so build (`cargo … --no-run`) *before* entering a
  `ulimit -v` cap; the scripts already do. A cap on a command that still has
  to link fails with `mold: cannot reserve … bytes of virtual memory`.
- **Never run `cargo fmt`** (any scope): the repo is deliberately not
  rustfmt-formatted (`issues/fmt-not-enforced-decision.md`); a formatting
  pass buries a real diff under ~18k lines of churn (it happened,
  2026-08-07). Match the surrounding style by hand.
- `Debug` on kernel `Term`/`Type`/`Level` etc. is **budget-bounded**
  (`crates/kernel/src/fmt.rs`: ≤512 nodes, ≤64 depth, `…` elision), so an
  accidental `{:?}` is safe and prints compact syntax. Keep it that way: any
  new recursive kernel type gets a `node()`-gated manual impl, never a
  derived `Debug`. In property tests still prefer seed-only failures (the
  `law!` macro in `crates/kernel/tests/subst_laws.rs`) — bounded output is
  for humans debugging one case, not 300 failing seeds.
- **Benchmarks: `scripts/bench`** (same `ulimit` discipline as `scripts/test`;
  never bare `cargo bench`). `--check` gates against
  `crates/kernel/benches/baseline.tsv`; the headline number is the scaling
  exponent, not the time. `docs/benchmarking.md` explains what "regressed"
  means and why the harness is first-party (the kernel stays at zero
  dependencies, dev-dependencies included — so no Criterion).
- **What is slow right now, and where it comes from: `scripts/perf report`**
  (`perf/README.md`). `scripts/perf snapshot` measures the suite history and
  a corpus of files cold/warm/edited through the release CLI with `--timings`
  and writes a dated, environment-keyed record to `perf/snapshots/`;
  `report` prints the phase split, the concentration per file and the
  heaviest declarations with deltas against the previous same-environment
  snapshot, and `serve` is the dashboard. Read the latest report before
  choosing a perf target, so a round attacks what the corpus says dominates
  and not the item it happened to be looking at. It is a diary, not a gate.
- **Did a change make it faster: `scripts/perf ab`** (`perf/README.md`). Never
  hand-roll a before/after pair: three attempts at one in a single session
  produced two wrong answers, each confidently. It builds both binaries,
  interleaves `--samples` cold checks, and reports **counters and seconds
  apart** — counters are exact on one tree and any column that moved is a
  behaviour change, while seconds get the per-sample spread beside the median
  and a delta inside that spread is reported as no result. `--base REV` builds
  the before side in a reused git worktree; `--patch FILE` reverses a diff in
  this tree instead, which is what a furnace box needs (no `.git`), and there
  `--touch` is mandatory — cargo will otherwise hand back the binary it already
  built, since a checkout's mtimes are the local ones against a `target/` that
  outlives instances, and the harness then refuses the run as comparing one
  binary with itself. `--marker COLUMN` asserts the after binary emits a new
  counter column and the before one does not. `--replay` re-renders the last
  report for free. **A change to `lib/` or a showcase is the other A/B**:
  `--source-patch FILE` holds the binary fixed and reverses the diff over the
  *sources* between samples (`--heather BIN` skips the build), defaults the
  corpus to the files the patch touched, and reports a moved counter as the
  round's result rather than as an alarm — term growth is what a readability
  round trades. It refuses a patch that touches `crates/`; that is `--patch`.
- **Read a `--timings` TSV with `scripts/timings`**, never by counting
  indices into an `awk -F'\t'` line — that mislabelled three columns in one
  session. It looks columns up by name and prints the five the design docs
  quote (`--diff a.tsv b.tsv` for per-item deltas). `queries` means every
  `Tc::conv_ty` query — shortcut + memo + miss; the attribution docs written
  before it quote `conv_shortcut_hits` alone, so reproduce one of their numbers
  with `--columns shortcut`. Counts are exact and worker-count-invariant;
  seconds are not, and at width > 1 item times sum past the run row.
- **Testing generated terms** (elaborator schemas, lowerings):
  `docs/testing-generated-terms.md` — the four axes a test has to vary
  (literal *and* neutral scrutinee, an **open** element type, a *checking*
  position and not only computation, and a negative control). Five live
  defects here were invisible to tests that varied none of them; three of the
  five were hidden by a closed type alone.
- **Showcases: `scripts/showcase`** over `docs/showcase/showcases.tsv`, the
  manifest that says which showcase is checked how, and against which `-L`
  dirs. `scripts/showcase check <name>` is the hand check with the `-L` set and
  the `ulimit` discipline already right (no `/tmp` copy: the loader searches the
  importing file's own directory first, so a sibling import needs no `-L`, and
  `-L docs/showcase` is the thing that breaks — it puts that directory's
  `parser_core` against the library's). A new file under `docs/showcase/` fails
  `crates/cli/tests/showcase.rs` until it declares a tier. `docs/showcase/calc_text.hthr`
  is gated by `showcase_gate` in `scripts/test` (full lane only, ~6 min): it
  cannot be a test target, at 334 CPU-s and 9.8 GiB against the runner's 300 s
  and 6 GiB rails.
- Issue tracker: `scripts/issue` over `issues/*.md` (see `issues/README.md`).
- Type-theory source of truth: `docs/delam/04–06`; `docs/delam/README.md`
  explains which chapters are implementation-relevant (01–03 are a
  simplified warm-up system, not the target).
- Kernel design decisions: `crates/kernel/DESIGN.md`.
