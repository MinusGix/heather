---
title: Hold the bounded Debug formatter's state in one enum
status: closed
labels: [kernel,state-machine,fmt]
area: kernel
created: 2026-11-08
updated: 2026-11-09
---

Hold the bounded `Debug` formatter's state in one enum, so `write_exact` nested inside a bounded `{:?}` cannot re-arm the budget or underflow the depth.

## Problem

`crates/kernel/src/fmt.rs` ~48–90 keeps three states (Idle, Bounded `{remaining, depth}`, Exact `{depth}`) in three thread-locals with a sentinel (`REMAINING < 0` means no format is in progress). The module guards exact mode entered from Idle (the counter starts at `isize::MAX`), but not `write_exact` called inside a bounded format. There the counter keeps falling from the bounded budget, crosses below zero, and the next node takes itself for outermost and resets `DEPTH` to 0. When the enclosing frames unwind, `DEPTH - 1` underflows. Reproduced with a throwaway unit test (a `Debug` impl calling `write_exact` on a 600-deep `Succ` chain inside `node`): in a debug build it panics with "attempt to subtract with overflow" at `fmt.rs:81` (`d.set(d.get() - 1)`); in release the depth wraps to `u32::MAX` and every later node of the outer format is elided.

Nothing calls `write_exact` from inside a `Debug` impl today (its callers are the metrics sampler and the elaborator tests' Ψ hash), so this is latent. But "an accidental `{:?}` is safe" is a rail CLAUDE.md relies on.

Review: `docs/kernel/kernel-implicit-state-review.md` §7.

## Proposal

`Cell<FmtState>` with `enum FmtState { Idle, Bounded { remaining, depth }, Exact { depth } }`. `write_exact`'s guard saves and restores the whole state, and `node`'s outermost test matches `Idle`. Add the reproducing test (a `Debug` impl calling `write_exact` on a 600-deep `Succ` chain inside `node`) to `fmt.rs`'s tests.

## Log
- 2026-11-09: done. One `Cell<FmtState>` (`Idle`, `Bounded { remaining, depth }`, `Exact`); `write_exact` saves and restores the whole state; an outermost node resets to `Idle` in a drop guard, so a panicking `Debug` impl cannot strand the thread mid-budget either. Regression test `fmt::tests::write_exact_inside_a_bounded_format_resumes_it` panics on the old code.
