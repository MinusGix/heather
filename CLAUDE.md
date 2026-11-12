# Heather — working notes for Claude

- **Run tests only via `scripts/test`** (wraps `cargo test` in `ulimit -v/-t`
  plus a thread cap). Never run bare `cargo test`: a runaway test or a
  Debug-formatted kernel term can OOM the whole machine, not just the process.
  - `scripts/test --fast` is the inner loop. It skips the whole-library
    acceptance tests, the perturbed-library mutation controls and the native
    x86 certificate gates (`crates/cli/tests/native*.rs`), and replays semantic
    test images an earlier compiler build wrote (vouched for by the verdict
    store at `target/decl-cache` or kernel-rechecked; the current frontend is
    not re-run on unchanged library modules, and a module whose dependency
    changed in a way it did not observe has its image moved instead,
    `docs/module-interface-cutoff-design.md`). What it skips is the `SKIP`
    list in `scripts/test`.
  - A round's **final** verification, and any change touching `lib/`, the kit
    or the generators, runs `scripts/test --pr`: the test files its diff
    from `origin/master` can affect (Cargo's dep-info, family members one
    by one, every run-time reader of `lib/` on a `lib/` change; anything it
    cannot place runs everything; `HEATHER_PR_AFFECTED=all` forces all, §2.2.1
    of the design note), over the same replayed images, and the native x86
    certificate gates (`crates/cli/tests/native*.rs`) shrink to one smoke
    unless the diff touches what they check (`lib/native`, the machine/OS
    models, `crates/cli/src/native`, the kernel; `HEATHER_PR_NATIVE=all`
    forces them). The exact image policy (plain `scripts/test`, which
    re-elaborates every library module after a compiler edit) is the nightly
    master sentinel's lane; run it yourself only when the round changes the
    image format, the caches or the loader (`crates/cache`,
    `crates/cli/src/semantic.rs`). Why: `docs/testing-architecture-design.md`.
    Docs-only or issue-only changes need no suite at all.
  - **A change to what the elaborator infers re-elaborates the whole
    library before it merges** (Minus, 2026-11-11): motive synthesis, the
    unifier, instance choice, defaults, any tactic or rewrite the library
    already calls. The fast and PR lanes replay unchanged library modules
    after a compiler edit, so they cannot see a proof the change moved
    (PR #566 merged three broken proofs that way). Run plain `scripts/test`
    (the exact image policy), or the sweep: every `lib/**/*.hthr` through
    `heather check --cache --expectations` with the new release binary and
    no `--accept-stale-images`, capped per file, three at a time. Group
    failures by the location of their first error: most are importers of
    one broken module.
  - **`HEATHER_CACHE_DIR`** moves every suite and gate store (the semantic,
    native and CLI image stores, `decl-cache`, and `heather check --cache`'s
    default) out of `target/`, so worktrees of this repo can share them
    (`issues/shared-cache-dir.md`). Never point two worktrees at one
    `CARGO_TARGET_DIR`: Cargo's mtime freshness then runs the other's build.
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
- **The kernel and elab libraries are packages of their own**:
  `heather-kernel-lib` and `heather-elab-lib` (`crates/*-lib/Cargo.toml`,
  pointing at `crates/kernel/src` and `crates/elab/src`; crate names still
  `heather_kernel`/`heather_elab`). They build at opt-level 3; `heather-kernel`
  and `heather-elab` keep the integration tests and benches at the dev
  profile's opt-level 0, so `-p heather-elab --test X` is unchanged. Cargo
  applies a package's opt-level to all its targets, which is why
  (`issues/fresh-container-compile-cost.md`). The kernel's unit tests are
  `-p heather-kernel-lib --lib`.
- **An elaborator method goes on its area's view, not on `Elaborator`**: each
  area's module defines `Area<'e>(&'e Elaborator)` for its `&self` methods and
  `AreaMut<'e>(&'e mut Elaborator)` for its `&mut self` ones, both
  dereferencing to the elaborator, and another area calls
  `Area(self).method(…)` (`crates/elab/src/lib.rs`'s module doc has the
  pattern and what differs: `self.0.clone()`, `self.0.a` for split borrows).
  rustc compiles all of one `Self` type's methods as one unit, wherever the
  `impl` blocks are written, so a method on `Elaborator` recompiles with
  everything else on it. **`scripts/codegen-units`** lists a build's units by
  size and what fills them; a unit that has grown back shows there.
  `scripts/rustc-wrapper` (wired in `.cargo/config.toml`) turns rustc's
  cross-unit optimisation pass off for the elaborator's incremental builds
  only, because there one edit redid it for the whole crate
  (`issues/elaborator-crate-compile-per-edit.md`).
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
    the declaration that was running; `compile-x86` leaves the
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
- **Cloud containers prebuild at session start**: `scripts/session-start`
  (the SessionStart hook in `.claude/settings.json`, active only when
  `CLAUDE_CODE_REMOTE=true`) installs mold and starts `cargo test --workspace
  --no-run` in the background, logging to `target/session-prebuild.log`. A
  first `scripts/test` that says it is waiting on Cargo's lock is waiting on
  that build, not stuck. `HEATHER_NO_PREBUILD=1` skips it.
- **Compiled Heather linked into Rust is `crates/linked`**: `generated/*.s`
  is `compile-x86`'s checked-in output for `generated/EXPORTS.tsv`, held to
  the compiler by `crates/cli/tests/native_linked.rs` (a native gate). After
  changing a linked module (`lib/native/crypto/`, `lib/lang/lexer/`), the
  lowering or the emitter, run **`scripts/linked`** to rewrite the files
  (`--check` compares; a row whose binary and import closure are unchanged
  is not recompiled) and the Rust declarations with them
  (`generated/exports.rs`, never edited: `tests/linked_exports.rs`); a new
  export is a line in the table (module, function, parameters, a span of
  bytes it reads as `name: span` and one it stores into as
  `name: span mut`; a method is named by its path, `List::f`, and exported
  under the symbol the path derives, `list_f`, or one written as
  `sym = List::f`; a fourth column names the export whose program the
  function is a function of, and it is then a label in that export's file,
  not a file), a wrapper in `src/`, and tests against
  an independent reference. Run `scripts/linked` before writing the
  wrapper: the compiler links this crate, so a wrapper of a symbol not yet
  generated stops the build that would generate it.
  A value the Rust reads the linked code's answers with is a `def` of the
  module (a numeral), a row of `generated/CONSTANTS.tsv`, and Rust's copy
  is `generated/constants.rs`, written by the same script (`TOKEN_END_BITS`).
  The `heather` binary links these files, so one that lost a symbol (a merge
  conflict taken from the wrong side) fails every build with `undefined
  symbol: scan_token`: restore a complete copy (`git checkout HEAD --
  crates/linked/generated/<file>.s`), build, then run `scripts/linked`
  (`issues/linked-assembly-bootstrap.md`).
  When `compile-x86` answers "the verified lowering refused this program
  with the planner's placement", it names the node refused, its place and
  what each register held (`lib/native/function_ir/function_ir_refusal.hthr`
  mirrors the emitter's tests). The function is usually fine and the
  placement is not: read the report beside `Node::choose_by` and
  `StructuredRegion::plan_in`
  (`issues/function-ir-planner-register-pressure.md`).
  The scanner (`src/scanner.rs`) is held to `heather_syntax::lex` by
  `tests/scanner.rs`; after changing its `PROBES` or the automaton, run
  **`scripts/lexer-probes`** to rewrite the evaluated probes in
  `lib/_tests/lang/lexer`.
- **`HEATHER_LEXER=linked`** has the `heather` binary cut every source with
  Heather's own scanner (compiled, linked; `heather_syntax::lexer::install_scanner`,
  `issues/self-lexer-linked.md`); values and every refusal stay the Rust
  lexer's, so output is unchanged, and `HEATHER_LEXER_REPORT=1` prints who cut
  what. Off by default. A new token kind is three numberings to extend:
  `lexer_scan.hthr`'s `KIND_*`, `heather_linked::scanner::Kind` and
  `heather_syntax::lexer::scan_code` (`crates/linked/tests/scanner.rs` holds
  them to each other).
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
- **Syntax is shared through the kernel's `Rc`**: `use heather_kernel::rc::Rc;`
  (`crate::rc::Rc` inside the kernel), never `std::sync::Arc` under an alias.
  It is `Arc` with a head in which the kernel keeps what it computed about
  the node (free-variable bounds, `crates/kernel/src/rc.rs`), and its API is
  `Arc`'s. An unsized payload (`[T]`, `str`, `dyn Trait`) is a plain `Arc`.
  A method cannot take `self: &Rc<Self>`; write it on `impl Rc<T>` in the
  kernel, or as an associated function.
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
- **Cloud timings are the reference** (Minus, 2026-10-29): record and compare
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
- **Testing generated terms** (elaborator schemas, lowerings):
  `docs/testing-generated-terms.md` — vary all four axes (literal *and*
  neutral scrutinee, an **open** element type, a *checking* position and not
  only computation, and a negative control); defects have hidden behind each.
- **Compilation design starts from `docs/compilation-vision.md`**: the
  settled principles (certificate logical, everything else operational;
  untrusted search over checked witnesses; prove the generator, not the
  copies; disciplines as libraries; opt-in, syntax-keyed `Compile(f)`) and
  the picture (languages producing `Compile(f)`, facts as side-proofs the
  compiler finds). A native, `runtime fn`, `Compile`, `datarepr` or pass
  round reads it before designing, and extends it rather than re-deriving it.
- **Writing proofs: `docs/proof-patterns.md`** has the rules rounds kept
  rediscovering (closed verdicts as `b = True` by `refl`, never `refl`
  between two computations, neutral parameters, stage theorems, what `omega`
  cannot read yet), each with its reason and the issue that would retire it.
  Correct it when a rule goes stale.
- **Module lists in Rust are closures, not hand edits**: a list of
  `("name", include_str!(…))` library modules is marked `// lib-closure:
  <roots>… [minus <roots>…]` and written by `scripts/lib-closures --fix`
  from the imports; `crates/cli/tests/lib_closures.rs` holds marked lists to
  the loader. After adding an `import` to a listed module, run the script.
  It also fails on a `lib/` module nothing reaches (the whole-library
  gate's orphan lint, in a second), and `scripts/test` runs it first.
- **Tactics build `Tac` values through calls**: `pure(a)`, `ask(r)`,
  `ask_then(r, k)`, never `Pure(…)`/`Ask(…)` as a value (patterns are
  free). A written tier-2 constructor re-spells `Tac`'s `W` encoding for the
  kernel at every occurrence and every wildcard copy (docs/grind-design.md
  §14.6, issues/tier2-constructor-value-cost.md).
- **Rust test or theorem: `docs/test-value-audit.md` §5.** If Heather can
  state a claim, write it in Heather. A library PR adds theorems to its module
  (a client would cite them) or probes to `lib/_tests` (mirrors `lib/`,
  `<subject>_tests` stems, never imported from outside), not a Rust test: the
  whole-library gate (`crates/cli/tests/library.rs`) checks every module. A
  false mathematical claim is a `¬` theorem, not a refusal. A refusal names
  its reason: in Heather, a declaration under `// expect-error: <what the
  error says>` (or `(kernel)`, `(mismatch)`), checked by `heather check
  --expectations`, which the gate passes (§4.3); in Rust,
  `support::assert_refused` with a `Refusal`. Never a bare `is_err()`.
- **Areas and importance: `docs/roadmap.md`** owns the project's areas, their
  priority, the milestones effort goes toward; read it before choosing what
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
