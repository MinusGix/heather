---
title: "~47 KB of stack per `Succ` level caps numerals at ~150"
status: open
labels: [elaboration, kernel, tooling]
area: kernel
created: 2026-07-27
updated: 2026-07-28
---

A numeral lowers to `Succ^n(Zero)` (`lib.rs`, `ExprKind::Num`), and something
on the elaborate-then-kernel-check path spends **~47 KB of stack per `Succ`
level**. `fn f() -> Nat { n }` alone therefore overflows at:

| stack | largest `n` that checks |
|---|---|
| 2 MiB (bare `cargo test`'s thread default) | ~40 |
| 8 MiB (`scripts/test`, and a main thread) | ~150 |

The depth is linear and small; the frames are not. That ratio is the bug —
47 KB per level of a three-field `Term::Succ` walk is two orders of magnitude
more than the data.

**Severity corrected 2026-07-27** (the first version of this issue overstated
it). `scripts/test` already sets `RUST_MIN_STACK=8388608`, so the sanctioned
runner has headroom to ~150 and no test in the suite is near it. The 2 MiB
figure applies to bare `cargo test`, which `CLAUDE.md` says never to run —
which is exactly how I met it. So this is a latent limit worth fixing, not a
live breakage, and the "raise the stack in `scripts/test`" mitigation is
already in place and was before this was filed.

**Not a records bug, and not new.** Verified against a clean tree at
51ba20a — the same program overflows there. Found while landing
[[surface-records]], where a test used `99` as a distinctive value and cost an
hour of bisection that looked like a projection loop.

## Why it matters beyond the annoyance

- The failure mode is bad: a stack overflow aborts the process, so one
  offending test takes down every other test in the same binary and the output
  names the wrong culprit or none. That is the part that cost the hour.
- It is a *latent* limit on what can be written at the surface at all, not
  just in tests. Nothing in the language says numerals are small, and ~150 is
  not a lot of headroom for, say, a table of constants in a generated IR.
- 47 KB per level is a symptom worth chasing on its own: whatever frame is
  that fat is on the path of *every* recursive walk, not only numerals.

## What to look at

Measure first — which frame is fat is not obvious from reading. Candidates, in
rough order of suspicion:

- Kernel conversion/reduction on a `Succ` spine (`conv.rs`, `reduce.rs`):
  large per-frame locals would explain the ratio.
- The elaborator's shift/substitution walks, which clone `Type` by value in
  several places.
- The declaration-level kernel re-check, which is the only thing that runs on
  a `fn f() -> Nat { 99 }` at all beyond building the term.

The fix is to shrink the frames. The harness mitigation is already in place
(`scripts/test` sets `RUST_MIN_STACK`), so there is nothing cheap left to
do — which is why this is filed as a real investigation rather than a
one-liner.

A binary numeral representation would dodge it and is *not* the fix — `Succ`
spines arise from ordinary recursion too, not only from literals.

## Log

- 2026-07-27: Filed while landing [[surface-records]]
  (docs/surface-records.md §11.3), after confirming against a clean tree that
  it predates the round.
- 2026-07-27: **Severity corrected the same day.** The first version said
  `scripts/test` "does not raise the stack"; it does, and has all along
  (`RUST_MIN_STACK=8388608`). I met this running bare `cargo test`, which is
  the thing `CLAUDE.md` exists to prevent. Re-measured properly: ~47 KB per
  `Succ` level, so ~40 at 2 MiB and ~150 at 8 MiB. Still worth fixing — the
  per-frame cost is on every recursive walk, not just numerals — but it is a
  latent limit, not a live breakage, and no test is near the bound.
- 2026-07-28: MEASURED, by the new bench suite's stack probe ([[kernel-benchmarks]]; `scripts/bench --stack-only`, which bisects the deepest numeral that check_term survives on a thread of exactly 4 MiB). Kernel-only check walk over Succ^n Zero: 53.9 KiB/level in the dev profile (76 levels in 4 MiB) versus 2.9 KiB/level in release (1414 levels) -- an 18x frame-size difference. Two consequences for this issue. (1) The ~47 KB/level headline is a DEV-PROFILE figure, and it reproduces without the elaborator, so the fat frames are the kernel's own recursion compiled without optimization. (2) The limit binds where scripts/test runs (debug) and is ~18x weaker in a shipped checker, so "a table of constants in a generated IR" is a test-profile worry first. Whatever the fix, the probe is the before/after number, and it is baselined.
