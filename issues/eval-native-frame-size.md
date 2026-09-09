---
title: A native evaluator re-entry costs kilobytes of stack, leaving one decade between answering and aborting
status: open
labels: [kernel,evaluator,performance]
created: 2026-09-09
updated: 2026-09-09
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
