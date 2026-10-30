---
title: Where the full lane's time goes after B1, and the duplicated work cut from it (2026-10-21)
status: open
labels: [testing,performance,tooling]
area: infrastructure
created: 2026-10-21
updated: 2026-10-30
---

The full lane is what most pull requests wait on, on a 4-CPU cloud container
and on the desktop. This re-reads it after B1 burned the wc command's tests
([[suite-iteration-chokepoints-2026-10]] left "re-read from the next suite's
timing table"), attributes it by target, test and declaration, and cuts the
duplicated work it found. Measured on one 4-CPU cloud container
(2026-10-21, master 7361ecc); read the ratios, not the seconds.

## Three runs a person actually waits on

The same suite costs very different amounts depending on what the box
already has. Each row is one `HEATHER_SUITE_DECLS=1 scripts/test` (the
per-test declaration rows are what the attribution below reads):

| run | what is cold | compile | tests wall | test CPU |
|---|---|---|---|---|
| fresh container | everything: target/, images, verdict store | 324 s | 506 s | 1287 s |
| warm, nothing changed | nothing | 0 | 281 s | 762 s |
| **after an elab Rust edit** (the usual PR) | every semantic test image (`Exact` policy); the verdict store stays warm | incremental | 418 s | 1103 s |

The test phase was **throughput-bound**: summed target seconds over the two
jobs the runner allowed on 4 CPUs is the wall, and the box averaged ~2.5 busy
CPUs. So the levers are total work and the job count, not the longest test.

## What was duplicated, and what changed

1. **Thirty-three test binaries rebuilt their "once per worker" base in every
   test.** They kept the base (a semantic image replay, or a library closure
   plus a probe module elaborated from source) in a `thread_local!`
   `OnceCell`, believing libtest reuses two worker threads. It does not:
   libtest runs every test on a fresh thread, so the cache was rebuilt per
   test (the per-test declaration rows show it: `lib_setoid_mergeable`
   replayed `list` 59 times, `operation_indexed_classes` elaborated `list`
   from source in each of its 23 tests). Image replays repeated beyond one per
   binary summed to ~92 s on a warm run, plus ~35 s of library modules
   elaborated from source per test in `lib_algebra`,
   `operation_indexed_classes`, `binder_symbol_notation` and
   `operators_onto_classes`. Now a process-wide `static … OnceLock`
   (`support::process_base` for the fallible bases, which also documents the
   pitfall), and `support::semantic_test_base` itself memoizes its replay per
   process and module list, which covers the callers that asked per call
   (`function_ir_loop_trace`'s checker, the read-loop fixture). What each test
   elaborates on top (its client, generated pieces, mutants) still reaches the
   real kernel every time; only the identical prefix is shared.
2. **The structured-block model was elaborated from source in fourteen tests
   across seven `function_ir_*` files** (~24 s). `function_ir_x86.rs`'s
   `structured_base()` elaborates it once per process.
   `recursive_physical_model_checks` keeps its own from-source check.
3. **`heather-export` built unoptimized.** `library_sweep` spent ~41 of its
   42 s outside elaboration, in the exporter; it was the warm lane's longest
   target. `opt-level = 3` like the other heavy crates: 42 → ~26 s (the rest
   is unprofiled, below).
4. **Two jobs on a 4-CPU box left a third of it idle.** A child is two libtest
   threads at kernel width one, and most targets spend their start waiting on
   one shared base, so a child averages ~1.3 busy CPUs. Below eight CPUs the
   runner now allows three children per four CPUs (`jobBounds`). Same box,
   warm, after the fixes above: 2 jobs 218 s → 3 jobs 165 s at the same CPU
   (577 s); 4 jobs 156 s, inside the noise, so three. Eight CPUs and up keep
   `floor(cores / 2) - 1`.

Also fixed on the way: `lib_std_float_error`'s module list elaborated
`ordered_field` before its import `semiring` (red on master since the two
merged; every test of the file failed in the fixture).

| run (same box) | before | after 1–3 | after 1–4 |
|---|---|---|---|
| warm, tests wall / CPU | 281 s / 762 s | 218 s / 578 s | 159 s / 554 s |
| elab edit, tests wall / CPU | 418 s / 1103 s | 350 s / 907 s | 242 s / 835 s |

(The "after 1–3" column is before `semantic_test_base`'s own per-process
memo; the last column has everything.)

Test counts are unchanged (3529 passed, 5 ignored, with the float_error fix).

## What is left, ranked

- **The fresh-container compile, 311 s (`cargo --timings`, cold).** The critical
  path is `heather-elab` at O3 (188 s), and `heather-elab-unit`, the same
  sources compiled a second time at O3 for the unit tests (160 s), runs beside
  it on the same four CPUs; then ~25 test binaries link. Only fresh cloud
  boxes pay it; the desktop edit loop is [[elab-rebuild-floor]]'s. No cheap
  lever found: elab-unit's own package is deliberate
  ([[elab-unit-tests-wait-on-cli-dev-dependency]]). Addressed by
  [[fresh-container-compile-cost]]: the tail after the lib was the
  integration-test binaries, compiled at O3 with their package.
- **Library images rebuilt after a Rust edit** (the `Exact` policy verifying
  the current frontend): once per build, gate vouched by the verdict store, so
  this is elaborator time. Heaviest per module (item seconds, one run):
  `creal` 33, `ordered_field` 25, `round` 21, `x86_64_asm_runs` 12, `wc` 10,
  `linux_x86_64_io` 10, `rat` 9. `lib_std_creal` builds its whole chain in one
  test (~72 s), the PR run's longest pole. These are elaboration-cost targets
  for those modules, not harness overhead.
- **`ir_v1`'s prefix in the certgen binaries**: ~29 s over 15 tests, and its
  rows still show ~20 s of kernel gate although the prefix runs under
  `with_decl_cache`. `certgen_emissions` is deliberately ungated (~4 s of it);
  why the gated ones still gate is unexamined. `certgen_controls` elaborates
  `LIB[..cut]` twice per test into the open `ir_v1` module, which a process
  image cannot share as is.
- **The prelude per test**: ~13 s over ~2300 tests (5–6 ms each), from every
  `Elaborator::with_prelude()`. A per-process prelude image would remove it.
- **`support::library` elaborates its closure from source once per process**,
  by design (the current frontend over every module): `list` ≈ 1 s in each of
  ~20 processes. Replaying the semantic images instead would save most of it
  but changes what those binaries exercise; Minus's call.
- **`library_sweep` at O3 is still ~26 s**, about 1 s of it elaboration; not
  profiled (no `perf` on the cloud box).
- **The desktop job bound is unmeasured.** Eight CPUs and up keep two-thread
  slots minus one; if children average ~1.3 busy CPUs there too, a 16-CPU box
  is also underused. `HEATHER_TEST_JOBS` cannot exceed the CPU bound, so
  measuring needs a one-line edit of `jobBounds`.

## Method

`HEATHER_SUITE_DECLS=1 scripts/test` writes every test thread's `--timings`
rows; summing item rows by (module, test) gives "module elaborated by N tests"
and summing module rows gives image replays per test. The runner's
`[start]`/`[done]` lines with per-target CPU give busy CPUs over time.

## Log

- 2026-10-21: Filed with the fixes above (thread-local bases, structured-block
  model, export opt-level, three jobs below eight CPUs, float_error order).
  Usual PR run (elab edit) on the 4-CPU box: compile 15 s + tests 418 s →
  tests 242 s; warm: 281 → 159 s. 3529 passed.
- 2026-10-22: The fresh-container compile item is
  [[fresh-container-compile-cost]] (libraries split into `-lib` packages so
  integration tests build at O0): cold compile 279 → 216 s on this box.
- 2026-10-23: Re-measured fresh / warm / elab-edit after #130 and #145 in
  [[testing-architecture]], which takes the suite-wide direction (post-merge
  sentinel, affected-target selection, single-flight image builds).
- 2026-10-30: The fresh-box profile's largest cost was the library gate run
  alone as a warmup and then again as a test; the runner now starts it first
  beside the targets that do not read its store ([[library-gate-warmup-runs-alone]]).
