---
title: One driver for the module pass's parallel/discard/serial-replay sequence; ticketed pool joins
status: open
labels: [elaboration,parallelism,refactor,state-machine]
area: infrastructure
created: 2026-11-02
updated: 2026-11-02
---

Make the module pass's parallel → join → discard → serial-replay sequence one driver with an explicit state, and make pool joins drain only what their caller submitted.

## Problem

`elab_module_source` and `check_module_source_inner` (`crates/elab/src/lib.rs` ~2490, ~3221) each write out the same sequence: clear the replay, take a checkpoint, run a pass with a `deferred_failed: &mut bool` out-parameter, and on a deferred failure restore the checkpoint and run `serially` (width 1, arm the replay, pass, finish the replay, restore the width). The state lives in the pool's width, that out-parameter, `ReplaySlot`'s `Option`, and `Replay { armed, live }` (three of four values reachable). Survey: `docs/elaborator/implicit-state-machines-survey.md` §2.

`KernelPool::join` takes every outstanding outcome, so only the pass that owns the queue may join. A slice replay inside a module pass once joined and took the pass's outcomes: a rejected proof became the slice's failure and the pass's own join found nothing (`module_delta.rs` ~1302). The fix was a per-site rule (don't join when you queued nothing), which the next nested user has to know too.

## Proposal

- `run_module_pass(kind, |me| pass)`: the one owner of checkpoint, discard and replay, used by both entry points.
- `Replay` as an enum: `Recorded`, `Replaying { at }`, `Dead`, with the timing folds carried across.
- Pool submissions return a ticket (or carry an epoch); `join(ticket)` drains only that caller's outcomes. This retires the nested-join class, not just the one instance.

No change to the width-independence contract or to what the caller sees.

## What it assumes from elsewhere

- **[[parallel-kernel-gate]]** owns the contract (`docs/kernel/parallel-kernel-gate-design.md` §5). Assumed here: only that the serial replay is the failure path.
- **[[deferred-gate-transitive-rollback]]** would replace the serial replay; the driver here is the seam it would plug into.
- **[[elab-field-lifetimes-explicit]]** groups the pool, replay and journal as module-pass state.

## Related

Filed together from the implicit-state-machines survey (`docs/elaborator/implicit-state-machines-survey.md`, 2026-11-02, ranked there): [[elab-field-lifetimes-explicit]], [[kernel-psi-bound-cache]], [[decl-attempt-lifecycle]], [[goal-slot-state-enum]], [[kernel-checker-mode-enum]].
