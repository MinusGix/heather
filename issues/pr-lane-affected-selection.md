---
title: Run only the test files a PR's diff can affect
status: closed
labels: [testing,performance]
area: infrastructure
created: 2026-10-30
updated: 2026-10-30
---

Built 2026-10-30 (Minus approved item 2 of the coordinator's suite-cost
list): unfiltered `scripts/test --pr` runs only what its diff from the
merge base with `origin/master` can affect, through
`scripts/affected-targets.mjs`. Design and the replay over sixty merges:
docs/infrastructure/testing-architecture-design.md §2.2.1. `HEATHER_PR_AFFECTED=all` runs
everything; `node scripts/affected-targets.mjs --manifest M --paths a,b`
prints what a list of files would select (M is `cargo test --workspace
--no-run --message-format=json`'s output).

What it reads: Cargo's dep-info for every unit (sources and `include_str!`
targets), the workspace's path dependencies (`cargo metadata --no-deps`),
build scripts' `rerun-if-changed` paths, the family root files' `mod`
declarations (members are selected one by one), and each test file's own
sources for run-time reads. What it cannot place runs everything.

What it does not narrow, on purpose:

- An edit to `crates/{kernel,syntax,elab}/src` still selects nearly every
  test, since every test links those libraries. Finer needs the coverage
  map of §2.2, which stays Minus's decision.
- A run-time reader (the library gate, the showcase, the native gates, the
  syntax corpus walks) runs on any change under `lib/`, `examples/`,
  `docs/showcase/` or the editor corpus: [[pr-affected-runtime-readers]].

The sentinel is the reference that would catch a miss; making its red runs
say whether `--pr` at the culprit merge selected the failing test is
[[pr-affected-sentinel-miss-report]].
