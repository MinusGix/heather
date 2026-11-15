---
title: Decide what the PR lane runs now that the native gates dominate it
status: closed
labels: [testing,performance,decision]
area: infrastructure
created: 2026-10-29
updated: 2026-10-29
---

A `scripts/test --pr` run for a parser change (PR #258's thread,
2026-10-29) took 2343 s: about 1200 s before the test phase and 1142 s of
tests (3649 target CPU-s, 275 targets, 3 jobs). Minus asked what changed,
since recent work was meant to stop rounds running everything.

## What `--pr` is

`--pr` was defined in #151 (2026-10-23) as "every test, over stale images":
it saves re-elaborating library modules after a compiler edit, not tests.
Affected-target selection (`--affected`, docs/infrastructure/testing-architecture-design.md
§2.2) was proposed there and left for Minus to decide after the sentinel had
run a while; it was never built. So nothing that selected tests regressed;
there was none.

## What made this run long

1. **No prebuild** ([[session-prebuild-skipped-by-snapshot]]): the compile
   ran cold in the foreground.
2. **Stale seed** ([[sentinel-images-not-published]]): the container seeded
   images from 2026-10-26, so the four serial warmups before the test phase
   (x86, omega, the native unit prefix, and the whole library gate as
   `cli_images_warmup`) elaborated much of the library cold.
3. **Native certificate gates grew.** At the last published sentinel
   (657094c, 2026-10-26 morning) the suite was 2192 target CPU-s and the
   native CLI gates were native_program 197, native_branches 66, native 3.
   `native_tools.rs` did not exist (added in #210 the same evening, then a
   test per round: #234 echo/yes STR, #245 cat FILE, #255 wc/head/decimals).
   On this run native_tools was 1078 CPU-s, native_cat 370, native_branches
   195: about 1640 CPU-s, 45 % of the suite. Showcase also went 127 → 432
   (243 on the 2026-10-29 sentinel, so part of 432 is the cold seed).
4. **Certificates are checked cold on every fresh box.** The verdict store
   is never seeded (by design: a vouched verdict skips the kernel), so every
   `write-elf` test kernel-checks its tool's certificate from scratch, for
   any change, including ones that cannot affect it. cat FILE's check alone
   passes the 300 s rail cold ([[native-tool-test-cold-certificate-rail]];
   #259 cuts the cold write-elf by about 30 %).

Items 1 and 2 are fixed by their issues. Items 3 and 4 are this issue.

## Options

- **A. `--pr` skips the native certificate gates unless the diff touches
  them**: `lib/native/**`, `lib/std/machine/**`, `lib/std/os/**`,
  `crates/cli/src/native/**`, `crates/kernel/src/**`, or the tests
  themselves. The sentinel runs them nightly and bisects. Other Rust edits
  (elab, syntax) would rely on the sentinel for these gates.
- **B. A. plus a smoke**: always run one small tool (yes or tr) end to end,
  so the write-elf path is exercised on every PR.
- **C. Keep `--pr` as every test**; rely on the two fixes above and #259.
  Expect ~25–30 min on a fresh box.

Recommended: B. The native gates are acceptance tests of a compiler
proved once; an elaborator or parser change that breaks them also breaks
the library gate or the smoke in almost every case, and the sentinel
catches the rest within a day.

## Log

- 2026-10-29: Minus chose B. `scripts/test --pr`, unfiltered, skips every
  `#[test]` in `crates/cli/tests/native*.rs` except
  `compiled_yes_runs_as_gnu_yes` unless `git diff` from the merge base with
  origin/master (untracked files included) touches `lib/native/`,
  `lib/_tests/native/`, `lib/std/machine/`, `lib/std/os/`,
  `crates/cli/src/native/`, `crates/cli/tests/native*`, `crates/kernel/src/`
  or `crates/kernel-lib/`. The names are read from the files, so a new gate
  is covered without editing the script. No merge base or
  `HEATHER_PR_NATIVE=all` runs them all. Decision logic checked by hand on
  this branch (23 skipped, the smoke kept), with an untracked file under
  `lib/native/` (none skipped), and with the override.
