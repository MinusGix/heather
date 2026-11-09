---
title: One type for the deferred-premise queues of conversion and the checker
status: open
labels: [kernel,state-machine,soundness,refactor]
area: kernel
created: 2026-11-08
updated: 2026-11-08
---

Give the deferred-premise discipline of the deep-term walks one type, shared by conversion and the checker, instead of eight hand-coordinated fields in `Conv` and four in `Tc`.

## Problem

`docs/deep-term-walks-design.md` §3.3–3.4: a premise met `SPINE_ITERATE_AT` frames deep is queued and judged before any verdict leaves. `Conv` (`crates/kernel/src/conv.rs` ~840–910) keeps this in `depth`, `deferred`, `deferred_pushed`, `provisional`, `attempts_open`, `defer_base`, `draining_at_top` and `defer_floor`, read with `memo` at seven sites (`tm`, `ty`, `tm_nat_tail`, `settle_at_top`, `drain_deferred`, `delta_lazy`, `memo_true`). A memo entry's state (final true, final false, provisional true) is split between a `bool` and membership in the `provisional` log. `Tc` (`typing.rs` ~1118–1137) has a simpler copy (`check_depth`, `deferred`, `deferred_pushed`, `defer_floor`) that takes memo entries back differently: it clears every memo after a refused root that queued anything (`forget_after_refusal`).

Two defects happened while this was built, both caught by the library gate: conjunction order (an expected `NotConvertible` became `OutOfFuel`, fixed by `defer_floor`), and a requeue loop inside a δ-attempt's drain (fixed by `defer_base`). It is soundness-relevant. A provisional `true` that outlived its dropped queue would make conversion accept a premise nobody judged. Today two `take_back_provisional` calls and the `attempts_open == 0` test prevent that. A third kind of speculation would have to remember all three.

Review: `docs/kernel-implicit-state-review.md` §2.

## Proposal

A `PremiseQueue<Item, Key>` owning the queue, floor, base, push epoch, provisional log and attempt count. Its API: `should_defer(depth)`, `defer(item)`, `context(|q| …)` for a root or popped item, `attempt(|q| …)` for speculation (mark, drain, truncate, take back), and `settle(result)`. A memo entry's three states become a value it owns. `Tc` uses the same type, which turns "take back provisional entries or clear everything" into one decision in one place.

This is `Conv::tm`'s prologue and epilogue, the hottest path in the kernel. The type must compile to today's field reads: `scripts/perf ab` with identical counters, and `scripts/bench --check`. The perturbed and library gates are the real test, since they found both earlier defects.

## Related

[[value-memo-evaluation-mode]], [[typing-memo-scope-key]], [[kernel-checker-mode-enum]] (a Locate checker bypasses the memo, so it shares the queue without the take-back question).
