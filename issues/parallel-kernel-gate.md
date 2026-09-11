---
title: Deferred kernel gate over Arc terms: check independent proofs on a worker pool while the elaborator continues
status: open
labels: [kernel,elaboration,parallelism,performance,design,cli]
created: 2026-09-11
updated: 2026-09-11
---

Check independent declarations' proofs on a pool of kernel workers while the elaborator continues serially: a deferred kernel gate behind the existing `KernelGate` seam, over `Arc` kernel terms.

## Why

The full lane's tail is five native certificate targets of one shape: thousands of small, successful, evaluator-bound theorems in a wide, shallow dependency graph ([[function-ir-x86-proof-scaling]] 2026-09-11: 3 474 items, 86 s kernel of 128 s, no failures). The kernel cannot check two of them at once because every term child is an `Rc`. Proof count only grows from here — no theorems about real programs are being checked yet.

The Arc-tax control ([[kernel-arena-terms-frozen-prefix]], 2026-09-11) says the serial cost of `Arc` is ~2% at module scale (1.04x bench median; 1.2–1.28x only on the refcount-dense nat micro-steps), so `Arc` plus a worker pool is affordable now; the arena representation remains the allocation project and is not what parallelism waits on.

## Design points (settled)

- **Deferred gate.** For each declaration: the statement's type is checked synchronously (dependents need it), the binding is committed to Ψ, and the proof/body check is queued with the Ψ prefix it must be checked against (Ψ is persistent — sealed chunks plus tail — so the snapshot is O(1)). The module joins all outstanding checks before it is accepted, published to any cache/image, or emitted (`build-x86` writes nothing before the join). Any failure fails the module, reported deterministically in declaration order.
- **`Arc` by alias** (`use std::sync::Arc as Rc` workspace-wide, as measured); a proper rename is a mechanical follow-up. Per-worker checker state (`Tc`, its `RefCell` memos, the value arena, `BodyCache`) — nothing shared but the frozen prefix.
- **Borrow the prefix, clone only what you build**: workers hold references into the shared prefix where the evaluator allows it; every avoided clone is both serial tax and contention removed. Audit the nat step paths' clone/drop pairs as part of this.
- **Worker count** from `--kernel-workers N` / `HEATHER_KERNEL_WORKERS`, default 1 = today's serial behaviour and error timing, so the test suite and its 4 GiB per-process rail are unchanged until the default moves.
- **Attribution survives.** The stats registry is thread-local; each worker's timers and counters are folded back into the declaration's row at join time, so `--timings` still reads kernel_gate per item.

## Measurement (the datum this round exists to produce)

`reused_callee` `build-x86`, release, warm image cache, same furnace instance, workers = 1, 2, 4, 8: wall, summed kernel_gate, peak RSS. Linear to 8 means contention is a non-issue; flat past 2 means the frozen-prefix borrow discipline or [[kernel-arena-terms-frozen-prefix]] comes first. Plus `scripts/bench --check` against a same-box Rc baseline to confirm the serial tax stayed where the control put it.

## What it assumes from elsewhere

- **[[parallel-checking-and-caching]]** owns cross-process parallelism and the shared telescope. Assumed here: only that in-process kernel parallelism is a component it can build on, not a replacement.
- **[[kernel-arena-terms-frozen-prefix]]** owns the representation question. Assumed here: the Arc-tax number, and that its scaling curve is an input to that decision.
- **[[perf-instrumentation-consolidation]]** owns the timers; the elaborator's serial 32 s is the wall right after this lands and needs its `other` bucket named.
