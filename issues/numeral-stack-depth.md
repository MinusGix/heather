---
title: A numeral above ~40 overflows a 2 MB stack
status: open
labels: [elaboration, kernel, tooling]
created: 2026-07-27
updated: 2026-07-27
---

```heather
fn f() -> Nat { 99 }
```

alone overflows a thread with a 2 MB stack — which is the default for a Rust
**test thread**, so any test that writes a largish numeral aborts the whole
test binary (`SIGABRT`, not a failure) rather than failing. 8 MB is enough for
`99`; the threshold is somewhere around 40.

A numeral lowers to `Succ^n(Zero)` (`lib.rs`, `ExprKind::Num`), so `99` is a
99-deep `Term`. Something on the elaborate-then-kernel-check path is spending
tens of kilobytes of stack per `Succ` level, which is the actual bug: the
depth is linear and small, the frames are not.

**Not a records bug, and not new.** Verified against a clean tree at
51ba20a — the same program overflows there. Found while landing
[[surface-records]], where a test used `99` as a distinctive value and cost an
hour of bisection that looked like a projection loop.

## Why it matters beyond the annoyance

- The failure mode is bad: a stack overflow aborts the process, so one
  offending test takes down every other test in the same binary and the output
  names the wrong culprit or none.
- It is a *latent* limit on what can be written at the surface at all, not
  just in tests. Nothing in the language says numerals are small.
- `scripts/test` caps threads and memory but does not raise the stack, so the
  suite is exactly where this bites.

## What to look at

Measure first — which frame is fat is not obvious from reading. Candidates, in
rough order of suspicion:

- Kernel conversion/reduction on a `Succ` spine (`conv.rs`, `reduce.rs`):
  large per-frame locals would explain the ratio.
- The elaborator's shift/substitution walks, which clone `Type` by value in
  several places.
- The declaration-level kernel re-check, which is the only thing that runs on
  a `fn f() -> Nat { 99 }` at all beyond building the term.

Two independent fixes, and they are not exclusive: shrink the frames (the real
fix), and/or give the test harness a bigger stack in `scripts/test` (the cheap
mitigation, which also stops one test from aborting its neighbours).

A binary numeral representation would dodge it and is *not* the fix — `Succ`
spines arise from ordinary recursion too, not only from literals.

## Log

- 2026-07-27: Filed while landing [[surface-records]]
  (docs/surface-records.md §11.3). Not investigated beyond confirming it
  predates the round and bisecting the threshold to ~40 at 2 MB.
