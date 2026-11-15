---
title: Testing architecture: a post-merge sentinel, affected-target selection, and the core changes that cut suite work
status: open
labels: [testing,performance,tooling,design]
area: infrastructure
created: 2026-10-23
updated: 2026-10-29
---

Minus (2026-10-23): the suite is slower than he would like, fresh box or
not. He wants either dramatic efficiency changes to the code (some held
back until Heather-in-Heather can vouch for them), or smarter testing:
quick, about the relevant area, with an alert when merged PRs interact
badly. The design and the options are in
`docs/infrastructure/testing-architecture-design.md`. This issue owns the measurements and
the decisions as they are taken.

## Measurements (2026-10-23, 4-CPU cloud container, master 1ae5dd6)

Plain `HEATHER_SUITE_DECLS=1 scripts/test`, three runs in one container,
3698 passed / 6 ignored in each:

| run | compile | tests wall | target CPU | item s | kernel gate | lib modules from source | of which repeats |
|---|---|---|---|---|---|---|---|
| fresh container | 205 s | 459 s | 1460 s | 1204 | 626 | 841 | 550 |
| warm, nothing changed | 0 | 162 s | 560 s | 452 | 229 | 87 | 75 |
| after an elab comment edit | 10 s | 240 s | 821 s | 641 | 234 | 281 | 133 |

"Repeats" are lib module seconds beyond each module's single cheapest
elaboration. In the fresh run they come from processes that miss the same
image key concurrently: `round` elaborated by the three `lib_std_float_*`
targets (~50–59 s each), `tactic` by `tactic_host`/`tactic_splits`/
`tactic_split_all` (~27 s each), `x86_64_stack_runs` by both
`function_ir_lower_*` (~28 s each), `ordered_field` three times (~15 s
each). Warm, the repeats are the by-design ones: `ir_v1` across certgen
targets (22 s), `list` (15 s) and `nat` (14 s) through `support::library`.

Warm, the tests' own modules are 358 of 452 item-seconds. The heaviest:
`bv_omega` 78 s (61 % gate; one `#[test]` running ~20 cases serially),
`heather` native unit tests 34 s, `function_ir_loop_trace` 29 s,
`function_ir_narrow_certificates` 28 s, `tactic_host` 25 s, `linux_wp` 24 s
(71 % gate). Image decode + recheck + publish is ~63 s of a warm run.

`linux_wp` passed cold in this container (81 s).

### Selection for lib-only PRs

Per-target library module sets taken from the fresh run's module/item rows,
with the target CPU from the same run. Over the 49 first-parent merges this
clone has, the ten lib-and-tests-only merges would have selected 22 %, 22 %,
31 %, 33 %, 44 % and five × 82 % of target CPU (82 % = they touched `nat`,
which sits under most of the suite). Of all 49 merges: ~9 docs/issues only,
~10 lib + tests only, ~30 touching `crates/elab/src` or `crates/kernel/src`
(where file-level selection selects every binary).

### Method

`target/suite-decls-full/` per run; item rows summed by module (lib module
= a basename of `lib/**/*.hthr`), threads per module counted from file
names, target CPU from `target/test-target-timings-full.tsv`. Scripts were
throwaway; the per-module and per-target sums are reproducible from the rows.

## Single-flight image builds (implemented 2026-10-23)

`ModuleImageCache::build_lock` (`crates/cache/src/module_image.rs`): a
`SemanticSession::check` miss takes an OS file lock on the key, loads again,
and builds only if still missing, holding the lock past publication
(`crates/cli/src/semantic.rs`). A hit takes no lock. Test:
`a_miss_waits_for_a_concurrent_build_of_the_same_key_and_replays_it`
(`crates/cli/tests/semantic.rs`), which fails with the lock disabled.

Same container, same tree plus the change, full lane:

| run | before | after |
|---|---|---|
| cold image + verdict stores, tests wall | 459 s | 318 s |
| cold, target CPU | 1460 s | 1046 s |
| cold, lib module repeats beyond the floor | 550 s | 205 s |
| after an elab edit, tests wall / CPU | 240 s / 821 s | 249 s / 822 s |

`round`, `tactic`, `x86_64_stack_runs` and `ordered_field` are each
elaborated once on a cold store now. The post-edit run does not move: there
the race barely happened (builds are short with the verdict store warm), and
its remaining repeats are the by-design ones (`ir_v1`, `list`, `nat`) plus
modules built under two different prefixes (`function_ir_lower_calls` in
both `function_ir_lower_*` targets), which is
[[relocatable-semantic-module-images]]'s. The "before" cold row is the
fresh-container run above, whose OS caches were also cold, so read the
ratio and not the seconds. 3699 passed (one new test).

## Minus's decisions (2026-10-23): sentinel, `--pr` lane, seeding

Built as `docs/infrastructure/testing-architecture-design.md` §5 describes. Same container,
full suite, 3699 passed in each:

| run | before | after |
|---|---|---|
| after an elab edit: plain (exact) → `--pr` | 240 s / 821 CPU-s | 182 s / 582 CPU-s |
| fresh thread's first suite: cold stores, plain → seeded images + `--pr` | 459 s / 1460 CPU-s | 201 s / 686 CPU-s |

The seeded run's verdict store was cold, as a fresh container's is: its
replays kernel-recheck the library (image decode + recheck ~93 s of item
time), which is the price of seeding images only.

`claude/sentinel-images` was first published by hand from master 1ae5dd6's
fresh green run (3698 passed) with this tree's image stores (the same
elaborator semantics identity: this PR changes no kernel, syntax or elab
source). Seeding takes ~2 s (a 33 MB archive).

The nightly scheduled task could not be created from the thread that built
this (a session once linked to a device cannot create a new-session-per-run
task); its prompt is in the project files (`testing/sentinel-scheduled-task.md`).

Seen on the way, not investigated: this container's session-start prebuild
logged only its start line, and the first `scripts/test` compiled from
scratch (205 s). The detached build seems to have died with the hook.

## Log

- 2026-10-23: Filed with the design note and the measurements above. Next:
  Minus's decisions in the note's §4 (sentinel, single-flight images first).
- 2026-10-23: Single-flight image builds implemented and measured (above):
  cold-store test phase 459 → 318 s; the post-edit run unchanged.
- 2026-10-23: Minus took the sentinel, the `--pr` lane and seeding;
  built and measured (above). Elab-edit PR run 240 → 182 s; a fresh
  thread's first suite 459 → 201 s.
- 2026-10-24: Test value (not cost) audited in `docs/test-value-audit.md`: what each kind of test buys, and the policy for when a PR adds a Rust test versus a theorem. Proposals: [[library-whole-check-gate]], [[refusal-tests-pin-their-reason]], [[library-tests-as-theorems]], [[hthr-test-corpus]].
- 2026-10-29: A fresh-box `--pr` run took 39 min. Neither prebuild nor
  seeding had been working ([[session-prebuild-skipped-by-snapshot]],
  [[sentinel-images-not-published]]), and the native certificate gates are
  now ~45 % of the suite; what the PR lane should run is
  [[pr-lane-cost-2026-10-29]].
- 2026-11-05: gardener: cites a file it shares with [[image-store-identity-overwrite]] (`crates/cache/src/module_image.rs`); [[perf-instrumentation-consolidation]] (`crates/cli/src/semantic.rs`); [[warm-replay-relocate-cost]] (`crates/cli/src/semantic.rs`).
