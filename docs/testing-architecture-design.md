# Testing architecture: what to make cheaper, and what to stop running

Status: design 2026-10-23. Minus's decisions the same day (§5): the
sentinel, a PR lane over stale images, and seeding fresh boxes. Those three
and single-flight image builds (§3.1.1) are implemented. Owner: `issues/testing-architecture.md`, which also holds the
measurements this note reads (box, commit, seconds). This note states costs
as shapes and ratios.

Minus's ask (2026-10-23): the suite is slower than he would like, fresh box
or not, and chipping at it target by target is not enough. Two directions:

- **Dramatic efficiency changes to the code itself**, including ones held
  back until Heather-in-Heather can vouch for an esoteric change to the core.
- **Smarter testing**: quick, about the relevant area, with a fuller run that
  raises an alert when several merged PRs interact badly.

This note reads where the time goes now (§1), then answers each direction
(§2, §3), and ends with an order of work and the decisions that are Minus's
(§4).

## 1. Where the time goes (2026-10-23, after #109, #130, #145)

Three runs of the plain full lane on one 4-CPU cloud box, each with
`HEATHER_SUITE_DECLS=1` so every test thread's declaration rows were kept.
The issue has the table; the shapes:

| run | what is cold | wall, relative to warm | test CPU, relative to warm |
|---|---|---|---|
| fresh container | `target/`, image store, verdict store | ~4x (compile is ~30% of it) | ~2.6x |
| after an elab edit (a comment is enough) | every semantic image (`Exact`) | ~1.6x | ~1.5x |
| warm, nothing changed | nothing | 1 | 1 |

Attribution, from the declaration rows (item seconds summed over every test
thread):

- **Warm, the suite is the tests' own work.** About four fifths of item time
  is the tests' own modules: generated certificates, mutants, probes. Half
  of it is kernel gate. The library prefix is replayed. What library work
  is left is by design (`support::library` elaborates `nat`/`list` from
  source once per process; certgen's `ir_v1` prefix per test), and it is a
  small share.
- **On a fresh box, almost half the item time is library modules elaborated
  more than once.** Every lib module that some test needs gets elaborated,
  which is the floor. On top of that, about twice the floor again goes to
  *the same module elaborated by several processes at once*: the three
  `lib_std_float_*` targets each build `round`/`ordered_field`, the three
  `tactic_*` targets each build `tactic`, both `function_ir_lower_*` targets
  build `x86_64_stack_runs`. They start together, all miss the empty image
  store, and none waits for another. `scripts/test` already works around
  this by hand for two prefixes (`semantic_x86_warmup`,
  `semantic_omega_warmup`); nothing covers the rest. The kernel gate also
  runs on everything, because the verdict store starts empty.
- **After an elab edit (the usual PR),** every image is stale under `Exact`,
  so every library module is re-elaborated once (the floor, with the kernel
  vouched by the warm verdict store). The repeats left are the by-design
  ones and the same module built under different prefixes. The concurrent
  race barely shows here: with the kernel vouched, builds are short and the
  targets drift apart before they collide.
- **The test phase is throughput-bound**, as #109 found: summed target CPU
  over the job count is about the wall. A single long test such as
  `bv_omega_suite`, which runs some twenty cases serially in one `#[test]`,
  moves the tail and not much else. Cutting total work is what helps.

What a PR touches decides which of these runs it pays. Over the last fifty
merges, about half touched `crates/elab/src` or `crates/kernel/src`, about a
fifth were `lib/` and tests only, and about a fifth were docs or issues only.

## 2. Smarter testing

Today there are two lanes, `--fast` and full, and nothing ever runs on
`master` itself. Every round's final check is a full run of its own branch.
If two PRs interact badly after both merged, the next thread that fetches
master is the one that finds out. That is the gap Minus named, and it is the
cheapest one to close.

### 2.1 A post-merge sentinel (implemented: `scripts/sentinel`)

A scheduled cloud session runs the full lane on a **fresh** container at
`master`'s head, nightly or after every few merges. If master is red, it
bisects across the PRs merged since the last green run, files an issue
naming the PR (or the pair of PRs) that broke it, and posts in the project
chat. If master is green, it records the timing table so the suite's growth
shows up in the history.

Why a fresh container on purpose: it is the one configuration nobody tests
locally, and it is where cold-only failures live. `linux_wp` at the CPU rail
on a cold image store is one. [[linux-wp-cold-rail]] closed it with #133,
and it is failing cold again (another thread has it as of this note), which
is the kind of regression a daily fresh-box run would have flagged. Each run's data would also have answered
this note's §1 without a hand measurement.

This needs no repository change, only a scheduled task in this project's
environment. It is Minus's call because it spends container time daily and
writes issues on its own. GitHub Actions is the alternative. Its runners
for a private repository are 2-core, and the free minutes would cover
roughly one full run a day, so the cloud session is the better host.

### 2.2 Affected-target selection for a PR

`scripts/test --affected [BASE]`: the targets whose inputs changed since
`BASE`, plus a fixed smoke set, instead of all of them. What decides
"inputs" differs by what changed.

- **`lib/` changes.** The per-test module rows already say which library
  modules each target's process used, transitively, because module lists
  are dependency-first. Recording that set for every run (cheaply, without
  the full declaration rows) gives an exact module → targets map. Measured
  against the fifty-merge history, it is **less selective than hoped**:
  `nat`, `list` and `bool` sit under most of the suite, and half the lib-only
  PRs touched one of them. A lib-only PR would run from about a fifth to
  about four fifths of the suite's CPU, depending on which modules it
  touched. That is worth having, but not a different regime.
- **Rust changes.** Cargo's dep-info files say which test binaries a
  source file reaches. For `crates/elab/src` and `crates/kernel/src` that is
  every binary, so file-level selection is useless for half the PRs.
  Selecting finer than that needs a *coverage map*: build once with
  `-C instrument-coverage`, run each target, and record which functions it
  executes. Then a diff's changed functions select the targets that run
  them. This is ordinary test-impact analysis, and its miss mode is known:
  a change to data or a constant that no changed function reads. The
  sentinel (§2.1) is what catches those misses. The map is rebuilt by the
  sentinel run, so it never goes far out of date.
- **Docs and issues only.** Already "no suite" by CLAUDE.md.

A cheaper middle step that needs no coverage: **memoize target results.**
A target whose test binary is byte-identical, and whose recorded runtime
inputs (images, the few lib files read at runtime) are unchanged since its
last pass, is not re-run. A lib-only PR relinks only the binaries that
`include_str!` a changed file, so the rest of the suite is skipped soundly.
An elab edit relinks everything, so it gains nothing there. Family binaries
share one binary across their member files, so a family is re-run whole.

### 2.3 What the lanes would mean

| lane | when | what runs |
|---|---|---|
| inner loop | while iterating | `--only`, one `--test`, `--fast` (as today) |
| PR | a round's final check | `--affected` + smoke, `Exact` images |
| sentinel | nightly / after merges, fresh box | everything, then bisect if red |

The policy change is CLAUDE.md's "a round's final verification is a plain
`scripts/test`". It would become "`--affected`", with the sentinel holding
the full gate. Minus decides that, and only after the sentinel has run for a
while, so its alerts show how often `--affected` would have missed.

## 3. Dramatic efficiency changes

Ordered by what they would need to be trusted, because that is the real
dividing line. Heather-in-Heather is needed only for changes to what the
**kernel** accepts or to how it decides. Everything above the kernel is
untrusted by construction: the elaborator, caches of its *search*, the
test harness. It can be as clever as we like, because the kernel rechecks
what it produces. That covers more of the suite's time than it sounds:
about half of item time is outside the kernel gate.

### 3.1 No trust question at all (can start now)

1. **Single-flight image builds.** The fresh-box finding. A per-key
   advisory lock in the image store (`std::fs::File::lock`, stable): the
   first process to miss a key builds and publishes it, and a second
   process that misses the same key blocks on the lock, then replays. This
   removes the concurrent repeats, which are about twice the floor on a
   fresh box (it does not move the post-edit run, where the race barely
   happens). **Implemented with this note**: on a cold store the full lane's
   test phase fell by about a third (the issue has the numbers). A process
   blocked on the lock spends no CPU, so the waiter's rail is safe. The two hand-written
   warm-ups stay, though, for their other reason: the first process to
   take a lock still pays the prefix *and* its own suffix under one rail.
   It is the cheapest, clearest win in this note.
2. **Seed a fresh box's image store from master.** The sentinel publishes
   `target/semantic-test-images` for the commit it tested, and a fresh
   session fetches it (in `scripts/session-start`, beside the prebuild).
   Images are kernel-rechecked on replay, so a downloaded image can at
   worst be a miss. This is not true of the *verdict* store, which skips
   the kernel. Seeding that would be rung-1 trust in a network artifact,
   so it is not proposed. Compile caching for fresh boxes (`sccache` over a
   remote bucket) is the same idea for rustc, and it needs a storage secret
   in the environment.
3. **Relocatable images / declaration-slice replay**
   ([[relocatable-semantic-module-images]], [[declaration-slice-replay]]),
   already designed. They make an image independent of the prefix it was
   built under, so a module is elaborated once per build, not once per
   distinct test module list. The prefix duplication measured here is
   modest (images on disk outnumber distinct modules by about a third), so
   this matters mainly for edit invalidation (`nat` edited invalidates
   everything after it). It is not the first lever. The edit-invalidation
   half has since landed as the early cutoff
   (`docs/module-interface-cutoff-design.md`): in the stale lanes, an
   unchanged module's image is moved across an upstream edit it did not
   observe, and the sentinel audits those moves against elaboration.
4. **Caching the elaborator's search across runs.** Omega/CutSat results,
   instance resolutions, and tactic scripts' successful paths, keyed by
   their canonical goal ([[persistent-certified-fact-cache]]). A hit is
   reconstructed and kernel-checked as usual, so a stale or wrong entry is
   a miss, never a false theorem. The tests' own work, which dominates a
   warm run, is largely elaboration of generated content, and much of it
   repeats goals from run to run.
5. **Compiler optimisation of the hot libraries.** PGO (and BOLT) on
   `heather-kernel-lib`/`heather-elab-lib`, trained on the suite. The source
   does not change, so trust does not either. Interpreter-shaped code is
   PGO's best case. It would be measured on Minus's machine with
   `scripts/perf ab`, not on a cloud box.
6. **Parallel elaboration of proof bodies** (Lean's trick, proofs opaque;
   [[parallel-checking-and-caching]]). This helps a single check's wall,
   not the suite, which is throughput-bound. It belongs on the editor and
   agent loop's list, not this one.

### 3.2 Trust-neutral, but a project in its own right

7. **Proof by reflection instead of generated certificates.** The heaviest
   warm targets (`function_ir_*`, `linux_wp*`, the native gates,
   `lib_std_float_arith`'s closed evaluation) check **large generated proof
   terms per program**. A checker written in Heather and proved once, and
   then *run* by the kernel on each program, replaces thousands of
   generated theorems with one evaluation. It uses only the existing kernel
   rules, so there is no new trust. It is also exactly Minus's 2026-10-21
   direction for native: a compiler proved once, not per-program proofs.
   That makes the native rebuild the single largest test-cost lever, as a
   side effect. The catch is that it turns proof-checking cost into
   **kernel evaluation cost**, which is what §3.3 is about.
8. **Certificate replay (rung 2 of [[parallel-checking-and-caching]]).**
   Cache the kernel's conversion *decisions* and replay them. The kernel
   still judges every step, so no new trust, but it changes the kernel's
   interface and so wants a careful round. The fresh-vs-replay divergence
   oracle comes free with it.

### 3.3 Needs Heather-in-Heather first

These change the trusted base. The standing position
([[perf-tracking-consistent-environment]] log, 2026-08-18) is that they land
once Heather can prove the property that makes them safe, and first in the
development fast mode.

9. **A compiled evaluator in the kernel.** A bytecode machine in the style
   of Coq's `vm_compute`, or native code (`native_compute`), for closed
   evaluation. With reflection (7) it is the dramatic combination: proofs
   become evaluations, and evaluations become compiled code. The trust
   argument writes itself from this project's own line. The native
   compiler, *proved correct in Heather*, is the evaluator, and its
   correctness theorem is the adequacy argument
   [[kernel-acceleration-policy]] asks representation changes for. That is
   the payoff that ties Heather-in-Heather, the native line and test speed
   together.
10. **Trusting cached verdicts and images in the final gate** (rung 3, a
    certified cache). Once the producer of an image or a verdict carries a
    proof about itself, the full lane may skip rechecking replayed images
    (a visible share of warm CPU) and verdicts on a fresh box.
11. **Arena / hash-consed kernel terms**
    ([[kernel-arena-terms-frozen-prefix]]). Already decided as "rewrite
    later, behind a named trigger", with an adequacy paragraph drafted.
    Nothing here moves that trigger.

## 4. Proposed order, and Minus's decisions

Cheap and clearly good, to implement once agreed:

1. **Single-flight image builds** (3.1.1). Done in the same PR as this
   note, measured on a cold store.
2. **The sentinel** (2.1). It needs Minus's yes on a recurring scheduled
   task, its cadence (nightly, or after N merges) and where it reports.
3. **Record each target's module set on every run** (the input to 2.2's
   `lib/` map and to the result memo). Then `--affected` for lib-only and
   test-only PRs, and the result memo.

Decisions that are Minus's:

- Whether the PR lane becomes `--affected` + smoke with the sentinel as the
  full gate (2.3), and when, given the sentinel's data.
- Whether to build the coverage map for Rust-edit selection (2.2). It is a
  real tool to maintain, and it is the only selection that helps half the
  PRs.
- Where the reflection direction (3.2.7) sits relative to the native
  rebuild that already wants it. This note argues they are the same work.
- Whether seeding fresh boxes from master (3.1.2) is worth a storage
  location for images (and later `sccache`).

## 5. Decided (Minus, 2026-10-23), and how it was built

Minus took the sentinel, a PR lane over stale images, and seeding fresh
boxes, and framed what is behind all of it: modules should be trusted and
shipped, and the arcane optimisations that would make invalidation fine
grained want Heather-in-Heather's proofs. The bridge until then is **two
tiers of trust**. A fast lane may use an optimisation nobody has proved; the
nightly sentinel runs the plain reference path and compares, so a divergence
names the optimisation that lied. Heather-in-Heather later promotes an
optimisation from "checked nightly" to "proven".

- **`scripts/test --pr`** is a round's final check: every test, with
  semantic images other builds wrote replayed (kernel-rechecked, or vouched
  for by the verdict store), so an elab edit no longer re-elaborates every
  library module. Plain `scripts/test` keeps the exact policy; a round runs
  it only when it changes the image format, the caches or the loader.
  Since 2026-10-29 the native certificate gates run in it only when the diff
  touches what they check, plus one smoke tool; the sentinel runs them
  nightly (issues/pr-lane-cost-2026-10-29.md).
- **`scripts/sentinel run`**, nightly from a scheduled cloud session on a
  fresh container at `master`: the exact-policy suite. Green, it publishes
  the image stores to the orphan branch `claude/sentinel-images` and reports
  targets whose CPU grew past the last green run's, and how many library
  images the current compiler elaborated differently from the last green
  run's (the stale lane's blind spot, made visible). Red, it bisects each
  failing target alone over the first-parent merges since the last green
  run, and the session files an issue naming the first failing merge.
- **Seeding**: on a fresh cloud box `scripts/test` first unpacks the
  sentinel's stores (`scripts/sentinel seed`). Images only: a seeded image
  is rechecked on replay, a seeded verdict would not be.
