---
title: Start the native certificate gates once their images exist, not after the whole library gate
status: open
labels: [testing, performance, images]
area: infrastructure
created: 2026-10-31
updated: 2026-10-31
---

Since [[library-gate-warmup-runs-alone]] the test runner starts the library
gate (`crates/cli/tests/library.rs`) first and holds `native_cat` and
`native_tools` until it has finished, because their `write-elf`s replay its
image store and, cold, would build most of the library themselves past the
CPU rail. But they replay only their own loads: the files they hand to
`write-elf` (all in `lib/native` and `lib/_tests/native`) and `write-elf`'s
fixed imports (`WRITE_ELF_IMPORTS`, inside `lib/native`'s closure). The rest
of the gate (`lib/std`'s tactic tests, the showcase-sized `_tests` folders,
the folder checks that follow the build step) is wall they wait through for
nothing. The tail of a fresh-box run was the gate followed by `native_tools`.

## Change

- `heather check --cache-dir D --unbuilt <paths>` names the modules of the
  paths' loads that `D` has no image of, in the loader's order, and exits 1
  while there are any. It is `--build-jobs`' plan (`BuildPlan`,
  `docs/module-dag-design.md` §12): keys chained up the import graph from
  image headers, nothing elaborated, under a second on the debug binary
  for `lib/native lib/_tests/native`.
- `PREREQUISITES` in `scripts/run-test-targets.mjs` names, per
  prerequisite, the folders whose loads its readers replay (`built`) and the
  store (`store`). While the gate runs, the runner asks the manifest's
  `heather` `--unbuilt` over them every ten seconds, under the lane's image
  policy (`--accept-stale-images` in the stale lanes, as the gate and
  `write-elf` do), and releases the readers the first time nothing is
  unbuilt (`[ready] library: … may start`). A module the gate cannot build
  is never built, so its readers fall back to waiting for the gate to
  finish, pass or fail, exactly as before. Warm, the first probe releases
  them at once.

Nothing a test checks moved: the same binaries, the same store, the same
rails; a released reader replays exactly the images it replayed before,
only earlier.

## Left

- The folders are a superset of what the readers load: `lib/_tests/native`
  holds probe modules (`native_compile_correct_tests`, …) no `write-elf`
  reads. Probing the exact files would release earlier but would drift
  from the tests' file lists; the folder rule cannot.
- A released reader runs beside the gate's build step, whose four children
  are its heaviest memory. The runner budgets the gate as one child.

## Log

- 2026-10-31: filed with the change above.
- 2026-10-31: Two `HEATHER_PR_NATIVE=all scripts/test --pr` runs on a
  4-CPU cloud box, both green (3653 passed). **Cold** (the change rebuilt
  every image): the gate ran 350 s and the probe released its readers at
  302 s, so the native closure finishes near the end of the build step
  (it is the longest chain, which `--build-jobs` starts first) and what is
  saved is the folder-check phase. Only one runner slot was free then:
  `native_cat` started 38 s later, and `native_tools`, which had no history
  in this lane and sorted after it, started when the gate ended, so the
  run's tail did not move. With the history that run wrote, `native_tools`
  goes first. **Warm**: the first probe released them 1 s into the gate's
  26 s; `native_tools` started at once and the test phase took 184 s.
- 2026-10-31: A cold build step with per-module times shows the native
  closure was not first in the queue. Ordered by source bytes, its modules
  waited behind the std test chains and were last built at about 200 s
  of 221 s, although the native chain itself was done by 89 s. The gate
  now builds the native folders' closures first (`--build-first`), and they
  are built by about 99 s with the step's length unchanged
  ([[native-closure-builds-first]]).
- 2026-11-05: gardener: cites a file it shares with [[early-cutoff-registry-and-order-granularity]] (`crates/cli/tests/library.rs`); [[pr-lane-prelude-change-images]] (`crates/cli/tests/library.rs`).
