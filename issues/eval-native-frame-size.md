---
title: A native evaluator re-entry costs kilobytes of stack, leaving one decade between answering and aborting
status: open
labels: [kernel,evaluator,performance]
area: kernel
created: 2026-09-09
updated: 2026-10-26
---

Filed out of [[kernel-native-depth-budget]], which had to pick a bound and found the two ends uncomfortably close.

Measured there (release and debug `heather check`, one furnace box, main-thread stack varied with `ulimit -s`, on `toNat(64, bitvec::add(64, ofNat(64, 0), ofNat(64, N)))`): one live re-entry of `Eval::drive` costs about 3.5 KB of stack in release and about 4 KB in debug, so an 8 MiB thread holds roughly 2000 of them (largest bound that answers instead of aborting: 1024 at 4 MiB, 2304 release / 2048 debug at 8 MiB, at least 5120 at 16 MiB).

Against that, real work already needs over 512: at `NATIVE_DEPTH_LIMIT = 512` the `conv/computed-numeral` bench family at n = 512 and the x86 native-certificate CLI tests both failed with `OutOfFuel`, and 576 fixed both. So the whole usable range is about one decade wide, and `NATIVE_DEPTH_LIMIT` was set to 1024 in the middle of it. That is a bound that works, not a bound with margin.

The interesting part is *why* a re-entry is that expensive. Two things point the same way. (1) The debug/release gap is almost absent here — about 4 KB against 3.5 KB — where the checking walk of [[numeral-stack-depth]] shows 18x (53.9 KiB against 2.9 KiB). So this is not unoptimized-build bloat: the frames are `drive`/`drive_from`/`step_eval`/`step_elim` carrying large `Work` and `Elim` locals by value, and optimization has nothing to remove. (2) `Work` and `Elim` are wide enums (an `Elim::App` alone carries two `Level`s and two closure pointers), and several are moved through the chain rather than borrowed.

Worth measuring before designing: `size_of` on `Work`, `Elim` and the `step_*` frames; which of the chain `drive -> drive_from -> step_eval/step_elim -> eval_tm/force -> drive` actually contributes; and whether boxing the cold `Elim` variants or splitting `step_elim`'s cold arms behind `#[inline(never)]` moves the number. The stack probe technique is `crates/kernel/benches/kernel/stack.rs`, which already bisects depth at a known stack size for the checking walk; this wants a sibling probe over the evaluator.

Halving the frame doubles the headroom at both ends at once, which is worth more than any further tuning of the bound.

## What it assumes from elsewhere

- **[[kernel-native-depth-budget]]** landed the bound and the measurements this issue starts from; the budget is what keeps the abort from happening while this is open.
- **[[numeral-stack-depth]]** is the same complaint about the *checking* walk, where the debug/release gap says the cause is different. A fix to either should be checked against the other's probe.

## Log

- 2026-10-26: Done (thread "Lift kernel evaluation depth limit"; design `docs/native-depth-budget-design.md` §8). Asked for by float literals: `Nat::pow(2, 1030)` refused on the budget, binary64 needs `2^1075`.

  Found: the live chain is not `drive -> step_eval -> drive` but fold classification. `pow(a, k+1) = pow(a, k) * a`, and classifying `mul`'s step probes `ih + pow(a, k)` transparently, which unfolds the inner power and classifies *its* step: `drive_from -> step_elim -> fold_run -> classify_step -> probe_step -> probe_apply -> delta_whnf -> drive`, one level per unit of the exponent. Frames read off `sub rsp` in the release binary: `drive_from` 2120 B (with `step_elim` inlined), `fold_run` 1304 B, `step_eval` 1320 B; `size_of::<Work>()` is 136 (`Elim` 128), so the frames are not big enums but the union of every arm's locals.

  Fix: a function a counted recursion passes through is a dispatcher; an arm that can re-enter gets a function of its own (`#[inline(never)]`). Boxing cold `Elim` variants was not needed and not done. Conversion shares the account, so it got the same treatment: `tm_ne`/`tm_nf` one function per arm, `rec_ca`'s 65-row tables built by `branch_table`. Measured per counted level (gdb backtrace at a 1 MiB main stack, release, cloud box): pow chain ~4.5 KB -> ~1.7 KB; conversion's neutral spine (`it(f, n, x) = it2(f, n, x)` by refl) ~3.1 KB -> ~1.7 KB; `rec_ca` frame 4144 B -> 616 B. New bench probe `stack/eval-nested-scrutinee` (512 KiB thread): master 134 levels (3.8 KiB/level), now 576 (910 B/level). `stack/check-numeral` unchanged (1462 levels in 4 MiB on both).

  `NATIVE_DEPTH_LIMIT` 1024 -> 2048: the worst counted chain now puts 2048 levels on under half the 8 MiB rail, the margin §4 chose. `pow(2, 1075)` checks; `pow(2, 2046)` (about 2050 levels) still refuses — that needs a 16 MiB rail and 4096, put to Minus as a decision. The small-step reducer (`step_term_frame`, ~3.7 KB) was not split and keeps 1024 as `REDUCER_DEPTH_LIMIT`; filed as [[reducer-step-frame-size]].
