---
title: A slice replayed at width > 1 under a verdict gate consumed the module pass's deferred kernel rejections
status: closed
labels: [soundness,kernel-gate,cache]
created: 2026-09-23
updated: 2026-09-23
---

Found 2026-09-23 while profiling slice replay for the certificate reorder (issues/check-module-delta-certificate-cost.md). Fixed the same day; this records what was open and for how long.

`Elaborator::recheck_extension` ended in an unconditional `self.kernel_pool.join()`. Its whole-module caller (`replay_module_delta`) runs at a module boundary with a quiescent pool, so that was right there. But a *slice* replay calls it with `on_pool == false` from inside a module pass, and that pass's own deferred theorem bodies are on the same pool. With no gate installed the function returned early, before the join; with one — and `heather check --cache` always installs the verdict store — it reached the join, which takes every outcome and clears the pool's failure flag.

So at width > 1 under `--cache`: a proof the elaborator passes and the kernel refuses, followed by an item whose slice replays (a proof-body edit keeps the prefix exact, which is exactly that shape), had its rejection taken as the *slice's* failure. The item was elaborated instead, the pass's own join found nothing, and the module checked with the refused proof in it. The kernel gate is the backstop for exactly the proofs the elaborator wrongly passes, so this was a fail-open in the backstop, at the default width. Width one was never affected (nothing is queued).

Fix: join only what the call itself queued — nothing when inline (`crates/elab/src/module_delta.rs`, the comment at the join). Regression test: `crates/elab/tests/slice_replay.rs::a_refused_proof_before_a_replayed_slice_still_refuses_the_module` (width 1 and 4, a gate that vouches for nothing); it failed at width 4 before the fix.

Exposure: `heather check --cache` of an edited module whose previous image is on disk, at width > 1. `build-x86` routed its certificate through the session only from 0901a9e5 (same day), and a generated certificate has no elaborator-passed kernel-refused proofs unless the generator or elaborator is wrong — which is the case the backstop exists for.
