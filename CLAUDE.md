# Heather — working notes for Claude

Notes for one area sit beside it and load when a session works there:
`crates/elab/CLAUDE.md`, `crates/kernel/CLAUDE.md`, `crates/linked/CLAUDE.md`,
`perf/CLAUDE.md`. This file holds what every round needs.

## Rails: every run is capped

- **Run tests only via `scripts/test`** (wraps `cargo test` in `ulimit -v/-t`
  plus a thread cap). Never run bare `cargo test`: a runaway test or a
  Debug-formatted kernel term can OOM the whole machine, not just the process.
- **Cap every direct `heather` run too**: deep conversion workloads are
  memory-superlinear. `target/release/heather check --limits dev <file>`
  (8 GiB of address space, 120 CPU-s, no core), loosening deliberately per
  run (`--limits dev,cpu=600`, `memory=16G`) — never uncapped. Every
  subcommand takes `--limits`, and `HEATHER_LIMITS=dev` in the environment
  does the same; it is off unless asked for, so it stays out of commands
  written for users (`crates/cli/src/limits.rs`). Keep `core=0` (in `dev`):
  a process killed at the rail otherwise writes a core of its full size.
  `cargo` and anything that is not `heather` still takes the shell's
  `ulimit`.
  - **To probe one declaration**: `--cache --only <item> --timings f.tsv`
    elaborates and gates just it over a replayed prefix
    (`docs/infrastructure/check-only-design.md`; the run is labelled and `scripts/timings`
    refuses to diff it against a whole run).
  - **A run killed at the rail still leaves its attribution**: a `--timings`
    table is appended as scopes close, and `<stem>.open.tsv` beside it names
    the declaration that was running; `compile-x86` leaves the
    certificate being checked as `<out>.certificate.unchecked.hthr`.
  - After editing the compiler's Rust, `--cache --accept-stale-images` replays
    the library's module images instead of re-elaborating them (the fast
    lane's trade; drop the flag for a final check).
- **Builds link with mold** (`.cargo/config.toml`), which reserves ~8 GiB of
  address space per link, so build (`cargo … --no-run`) *before* entering a
  `ulimit -v` cap; the scripts already do. A capped command that still has to
  link fails with `mold: cannot reserve … bytes of virtual memory`.
- **Never run `cargo fmt`** (any scope): the repo is deliberately not
  rustfmt-formatted (`issues/fmt-not-enforced-decision.md`); a formatting pass
  buries the real diff under thousands of lines of churn. Match the
  surrounding style by hand.

## Which test lane

| What the round is doing | Run |
|---|---|
| Docs-only or issue-only change | no suite at all |
| Inner loop while editing | `scripts/test --fast` |
| A round's **final** verification; any change touching `lib/`, the kit or the generators | `scripts/test --pr` |
| A change to what the elaborator infers | plain `scripts/test`, or the library sweep, before it merges |
| A change to the image format, the caches or the loader (`crates/cache`, `crates/cli/src/semantic.rs`) | plain `scripts/test` |
| A change to the kernel's traversals or bounds memo | `scripts/test --long` (own target dir) as a sweep, not a gate |

The header of `scripts/test` says exactly what each lane runs and skips; why
the lanes are cut this way is `docs/infrastructure/testing-architecture-design.md`.

- **`--fast` and `--pr` replay semantic images an earlier compiler build
  wrote** instead of re-elaborating unchanged library modules (a module
  whose dependency changed in a way it did not observe has its image moved,
  `docs/infrastructure/module-interface-cutoff-design.md`). Plain
  `scripts/test` is the exact image policy, which re-elaborates every library
  module after a compiler edit; it is the nightly master sentinel's lane, so
  run it yourself only for the two rows above that name it.
- **`--fast` and `--pr` run the `heather` binary with the kernel's sampled
  self-checks off** (`HEATHER_KERNEL_SELF_CHECKS=off`): the sample is most of
  a `runtime fn` generator module's check under the test profile
  (`issues/kernel-self-check-cost-on-skipped-terms.md`). To time a module as
  those lanes see it with `target/debug/heather`, set it too.
- **`--fast`** also skips the whole-library acceptance tests, the mutation
  controls and the native x86 certificate gates
  (`crates/cli/tests/native*.rs`): the `SKIP` list in `scripts/test`.
- **`--pr`** runs only the test files its diff from `origin/master` can
  affect, and one smoke of the native gates unless the diff touches what they
  check. `HEATHER_PR_AFFECTED=all` and `HEATHER_PR_NATIVE=all` force the rest.
- **A change to what the elaborator infers re-elaborates the whole library
  before it merges**: motive synthesis, the unifier, instance choice,
  defaults, any tactic or rewrite the library already calls. The fast and PR
  lanes replay unchanged library modules after a compiler edit, so they cannot
  see a proof the change moved. Run plain `scripts/test`, or the sweep: every
  `lib/**/*.hthr` through `heather check --cache --expectations` with the new
  release binary and no `--accept-stale-images`, capped per file, three at a
  time. Group failures by the location of their first error: most are
  importers of one broken module.

## Running the suite

- The suite ends with one `== suite: N passed, … ==` line; read that rather
  than grepping and summing. `INCOMPLETE` means a test binary died (usually
  the ulimit) and the counts are partial, not a smaller green suite.
- Run the full suite **in the background** and do doc/bookkeeping work while
  it runs; don't sleep-poll it.
- **The kernel and elab libraries are packages of their own**:
  `heather-kernel-lib` and `heather-elab-lib` (`crates/*-lib/Cargo.toml`,
  pointing at `crates/kernel/src` and `crates/elab/src`; crate names still
  `heather_kernel`/`heather_elab`). They build at opt-level 3; `heather-kernel`
  and `heather-elab` keep the integration tests and benches at the dev
  profile's opt-level 0, so `-p heather-elab --test X` is unchanged. Cargo
  applies a package's opt-level to all its targets, which is why
  (`issues/fresh-container-compile-cost.md`). The kernel's unit tests are
  `-p heather-kernel-lib --lib`; elab's are `-p heather-elab-unit --lib`, not
  `-p heather-elab --lib`.
- **The kernel gate runs eight workers by default** (`HEATHER_KERNEL_WORKERS`,
  `--kernel-workers`); item timings compare only at the same width, and
  `HEATHER_KERNEL_WORKERS=1` isolates one item. **`scripts/test` runs its
  children at width one** (the runner already parallelises targets, and the
  CPU rail counts every worker thread), so suite timings are width-one
  timings; an explicit `HEATHER_KERNEL_WORKERS` still wins. The suite's
  per-process address-space rail is 6 GiB.
- **`HEATHER_CACHE_DIR`** moves every suite and gate store (the semantic,
  native and CLI image stores, `decl-cache`, and `heather check --cache`'s
  default) out of `target/`, so worktrees of this repo can share them
  (`issues/shared-cache-dir.md`). Never point two worktrees at one
  `CARGO_TARGET_DIR`: Cargo's mtime freshness then runs the other's build.
- **Cloud containers prebuild at session start** (`scripts/session-start`,
  logging to `target/session-prebuild.log`). A first `scripts/test` that says
  it is waiting on Cargo's lock is waiting on that build, not stuck.
  `HEATHER_NO_PREBUILD=1` skips it.

## Read before choosing or designing

- **Areas and importance: `docs/roadmap.md`** owns the project's areas, their
  priority, the milestones effort goes toward; read it before choosing what
  a round works on. Every open issue carries `area:` (and `milestone:` when it
  serves one); `scripts/issue areas` is the overview.
- **Compilation design starts from `docs/compilation-vision.md`**: the
  settled principles and the picture. A native, `runtime fn`, `Compile`,
  `datarepr` or pass round reads it before designing, and extends it rather
  than re-deriving it.
- **Writing proofs: `docs/proof-patterns.md`** has the rules rounds kept
  rediscovering (closed verdicts as `b = True` by `refl`, never `refl`
  between two computations, neutral parameters, stage theorems, what `omega`
  cannot read yet), each with its reason and the issue that would retire it.
  Correct it when a rule goes stale.
- **Testing generated terms** (elaborator schemas, lowerings):
  `docs/testing-generated-terms.md` — vary all four axes (literal *and*
  neutral scrutinee, an **open** element type, a *checking* position and not
  only computation, and a negative control); defects have hidden behind each.
- Type-theory source of truth: `docs/delam/04–06`; `docs/delam/README.md`
  explains which chapters are implementation-relevant (01–03 are a
  simplified warm-up system, not the target).
- Kernel design decisions: `crates/kernel/DESIGN.md`.

## Conventions

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
- **Module lists in Rust are closures, not hand edits**: a list of
  `("name", include_str!(…))` library modules marked `// lib-closure: …` is
  written by `scripts/lib-closures --fix` from the imports (the script's
  header has the marker's grammar). After adding an `import` to a listed
  module, run it. It also fails on a `lib/` module nothing reaches, and
  `scripts/test` runs it first.
- **Tactics build `Tac` values through calls**: `pure(a)`, `ask(r)`,
  `ask_then(r, k)`, never `Pure(…)`/`Ask(…)` as a value (patterns are
  free). A written tier-2 constructor re-spells `Tac`'s `W` encoding for the
  kernel at every occurrence and every wildcard copy (docs/tactics/grind-design.md
  §14.6, issues/tier2-constructor-value-cost.md).
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
  through `scripts/perf ab`; read `perf/CLAUDE.md` first. Docs and these
  files state costs as shapes (exponents, what dominates), never as concrete
  numbers — those go stale. A `--timings` TSV is read with `scripts/timings`,
  never by counting `awk` column indices.
- Issue tracker: `scripts/issue` over `issues/*.md` (see `issues/README.md`).
  The issue files are the only tracked state: there is no committed index.
  `scripts/issue index` prints the one-line-per-issue overview to stdout and
  `scripts/issue list` the table; never commit an `INDEX.md`.
- **Docs: `docs/README.md` is the map**; a new doc goes in its area's
  folder there, and a later round extends its subject's doc. A doc whose code is deleted or
  replaced leaves in the same change: deleted if nothing live cites it (its
  mentions become `docs/<name>.md@<rev>`), moved to `docs/archive/` if code
  still cites its sections. Papers go in `docs/papers/` with a row in its
  README.
- Commit a completed issue fix once it is verified. Keep commits narrowly
  scoped, with descriptive messages, so small iterations are easy to resume
  across sessions.

## Native and linked code

- **Compiled Heather linked into Rust is `crates/linked`**; read
  `crates/linked/CLAUDE.md` before touching it, adding an export or a token
  kind, or using `HEATHER_LEXER=linked`. After changing a linked module
  (`lib/native/crypto/`, `lib/lang/lexer/`), the lowering or the emitter, run
  **`scripts/linked`** to rewrite its checked-in assembly (`--check`
  compares). A build that fails with `undefined symbol: scan_token` is one of
  those files having lost a symbol: `git checkout HEAD --
  crates/linked/generated/<file>.s`, build, then run `scripts/linked`.
- When `compile-x86` answers "the verified lowering refused this program
  with the planner's placement", it names the node refused, its place and
  what each register held (`lib/native/function_ir/function_ir_refusal.hthr`
  mirrors the emitter's tests). The function is usually fine and the
  placement is not: read the report beside `Node::choose_by` and
  `StructuredRegion::plan_in`
  (`issues/function-ir-planner-register-pressure.md`).
