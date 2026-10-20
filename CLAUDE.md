# Heather — working notes for Claude

- **Run tests only via `scripts/test`** (wraps `cargo test` in `ulimit -v/-t`
  plus a thread cap). Never run bare `cargo test`: a runaway test or a
  Debug-formatted kernel term can OOM the whole machine, not just the process.
  - `scripts/test --fast` is the inner loop. It skips the whole-library
    acceptance tests, the perturbed-library mutation controls and the native
    x86 certificate gates (`crates/cli/tests/native*.rs`), and replays semantic
    test images an earlier compiler build wrote (vouched for by the verdict
    store at `target/decl-cache` or kernel-rechecked; the current frontend is
    not re-run on unchanged library modules). What it skips and what dominates
    the rest: `issues/certgen-harness-cost.md`,
    `issues/native-summary-test-cpu-margin.md`.
  - A round's **final** verification, and any change touching `lib/`, the kit
    or the generators, runs the plain full `scripts/test`, which rebuilds those
    images. Docs-only or issue-only changes need no suite at all.
  - `scripts/test --long` (own target dir) also runs every slow kernel
    self-check every time (`crates/kernel/src/checks.rs`; the default samples
    one in sixteen) — a sweep for rounds touching the kernel's traversals or
    bounds memo, not a gate.
  - The suite ends with one `== suite: N passed, … ==` line; read that rather
    than grepping and summing. `INCOMPLETE` means a test binary died (usually
    the ulimit) and the counts are partial, not a smaller green suite.
  - Run the full suite **in the background** and do doc/bookkeeping work while
    it runs; don't sleep-poll it.
- **elab's unit tests (`crates/elab/src`) build and run as the
  `heather-elab-unit` package** (`scripts/test -p heather-elab-unit --lib`),
  not `-p heather-elab --lib`: a package of their own keeps their compile off
  the heather-cli dev-dependency chain
  (`issues/elab-unit-tests-wait-on-cli-dev-dependency.md`).
- **Cap every direct `heather` run too**: deep conversion workloads are
  memory-superlinear. `(ulimit -v 8388608 -t 120 -c 0; target/release/heather
  check <file>)`, loosening deliberately per run — never uncapped. Keep
  `-c 0`: a process killed at the rail otherwise writes a core of its full size.
  - **To probe one declaration**: `--cache --only <item> --timings f.tsv`
    elaborates and gates just it over a replayed prefix
    (`docs/check-only-design.md`; the run is labelled and `scripts/timings`
    refuses to diff it against a whole run).
  - **A run killed at the rail still leaves its attribution**: a `--timings`
    table is appended as scopes close, and `<stem>.open.tsv` beside it names
    the declaration that was running; `build-x86`/`compile-x86` leave the
    certificate being checked as `<out>.certificate.unchecked.hthr`.
  - After editing the compiler's Rust, `--cache --accept-stale-images` replays
    the library's module images instead of re-elaborating them (the fast
    lane's trade; drop the flag for a final check).
- **The kernel gate runs eight workers by default** (`HEATHER_KERNEL_WORKERS`,
  `--kernel-workers`); item timings compare only at the same width, and
  `HEATHER_KERNEL_WORKERS=1` isolates one item. **`scripts/test` runs its
  children at width one** (the runner already parallelises targets, and the
  CPU rail counts every worker thread), so suite timings are width-one
  timings; an explicit `HEATHER_KERNEL_WORKERS` still wins. The suite's
  per-process address-space rail is 6 GiB.
- **Builds link with mold** (`.cargo/config.toml`), which reserves ~8 GiB of
  address space per link, so build (`cargo … --no-run`) *before* entering a
  `ulimit -v` cap; the scripts already do. A capped command that still has to
  link fails with `mold: cannot reserve … bytes of virtual memory`.
- **Never run `cargo fmt`** (any scope): the repo is deliberately not
  rustfmt-formatted (`issues/fmt-not-enforced-decision.md`); a formatting pass
  buries the real diff under thousands of lines of churn. Match the
  surrounding style by hand.
- `Debug` on kernel `Term`/`Type`/`Level` etc. is **budget-bounded**
  (`crates/kernel/src/fmt.rs`: ≤512 nodes, ≤64 depth, `…` elision), so an
  accidental `{:?}` is safe. Keep it that way: any new recursive kernel type
  gets a `node()`-gated manual impl, never a derived `Debug`. Property tests
  still report seeds only (the `law!` macro in
  `crates/kernel/tests/subst_laws.rs`).
- **Perf measurement is not part of an ordinary round.** Elaborator changes —
  even complex ones, as long as they add no inference route on a hot path —
  land without timing anything; `scripts/bench --check` catches regressions.
  Only a round whose issue names performance as the point measures, and then
  through `scripts/perf ab`. Docs and this file state costs as shapes
  (exponents, what dominates), never as concrete numbers — those go stale.
- **Benchmarks: `scripts/bench`** (same `ulimit` discipline; never bare
  `cargo bench`). `--check` gates against `crates/kernel/benches/baseline.tsv`;
  the headline number is the scaling exponent, not the time.
  `docs/benchmarking.md` explains "regressed" and why the harness is
  first-party (the kernel has zero dependencies, dev-dependencies included).
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
- **Testing generated terms** (elaborator schemas, lowerings):
  `docs/testing-generated-terms.md` — vary all four axes (literal *and*
  neutral scrutinee, an **open** element type, a *checking* position and not
  only computation, and a negative control); defects have hidden behind each.
- **Areas and importance: `docs/roadmap.md`** owns the project's areas, their
  rank, and the milestones effort goes toward; read it before choosing what
  a round works on. Every open issue carries `area:` (and `milestone:` when it
  serves one); `scripts/issue areas` is the overview.
- Issue tracker: `scripts/issue` over `issues/*.md` (see `issues/README.md`).
  The issue files are the only tracked state: there is no committed index.
  `scripts/issue index` prints the one-line-per-issue overview to stdout and
  `scripts/issue list` the table; never commit an `INDEX.md`.
- Type-theory source of truth: `docs/delam/04–06`; `docs/delam/README.md`
  explains which chapters are implementation-relevant (01–03 are a
  simplified warm-up system, not the target).
- Kernel design decisions: `crates/kernel/DESIGN.md`.
