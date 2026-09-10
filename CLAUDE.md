# Heather — working notes for Claude

- **Run tests only via `scripts/test`** (wraps `cargo test` in `ulimit -v/-t`
  plus a thread cap). Never run bare `cargo test`: a runaway test or a
  Debug-formatted kernel term can OOM the whole machine, not just the process.
  `scripts/test --fast` (minutes, not seconds; what it skips and what
  dominates what remains live in `issues/certgen-harness-cost.md`) skips the
  whole-library acceptance tests, the perturbed-library mutation controls
  (~4.7 CPU-min), and the native x86 certificate gates
  (`crates/cli/tests/native*.rs` plus their warmup, ~20 CPU-min;
  `issues/native-summary-test-cpu-margin.md`) for the inner loop, and replays semantic test images that
  an earlier build of the compiler wrote (kernel-rechecked, but the current
  frontend is not re-run on unchanged library modules); a round's **final**
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
  the point measures, and then via the recorded protocol.
- **The same goes for direct `heather` runs**: deep conversion workloads are
  memory-superlinear (an uncapped release `heather check` on a deep-fuel IR
  theorem hit ~22 GB, 2026-07-31). Wrap every invocation:
  `(ulimit -v 8388608 -t 120; target/release/heather check <file>)`,
  loosening deliberately per run if needed — never uncapped. After editing
  the compiler's Rust, `--cache --accept-stale-images` replays the library's
  module images instead of re-elaborating them (same trade as the fast
  lane; drop the flag for a final check).
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
- **Testing generated terms** (elaborator schemas, lowerings):
  `docs/testing-generated-terms.md` — the four axes a test has to vary
  (literal *and* neutral scrutinee, an **open** element type, a *checking*
  position and not only computation, and a negative control). Five live
  defects here were invisible to tests that varied none of them; three of the
  five were hidden by a closed type alone.
- Issue tracker: `scripts/issue` over `issues/*.md` (see `issues/README.md`).
- Type-theory source of truth: `docs/delam/04–06`; `docs/delam/README.md`
  explains which chapters are implementation-relevant (01–03 are a
  simplified warm-up system, not the target).
- Kernel design decisions: `crates/kernel/DESIGN.md`.
