---
title: Deferred gate failure path: transitive rollback and cone-vouching instead of a serial replay
status: open
labels: [elaboration,kernel,parallelism,caching,design,diagnostics]
area: infrastructure
created: 2026-09-11
updated: 2026-09-11
---

Make the deferred kernel gate's failure path canonical instead of replaying the module serially: on a rejected proof, roll back the failed declaration and its transitive dependents, and have the cache vouch only for declarations whose whole dependency cone passed.

## Where this comes from

[[parallel-kernel-gate]] (2026-09-11) checks proofs on a worker pool while the elaborator continues, which means a declaration is committed to Ψ before its proof verdict is known. Around a *rejected* proof that changes what the elaborator observes, in increasing order of importance:

1. error order — the rejection surfaces at the join or the next poll, after later declarations' diagnostics;
2. the error set — dependents of a bad declaration succeed instead of failing with "unknown name", and side registrations differ (the traits fixture: a first instance with a false theorem is registered when the second arrives, so the second is refused as a duplicate);
3. cache soundness — a declaration checked after the bad one was checked against a Ψ containing an ill-typed body, and if that body is a definition, dependents' conversions may have unfolded it; the kernel's guarantee is relative to a well-formed Ψ, so such a verdict cannot be vouched for as a standalone fact.

The landed contract (`docs/kernel/parallel-kernel-gate-design.md` §5.1) makes width independence true by construction: a failed parallel pass is discarded to a module-entry checkpoint and the module re-run serially, with early abort on the first failed verdict, and a failing join vouches for nothing. Cost: a failing module pays the parallel prefix up to the abort plus the serial run — roughly what it cost before the pool existed. Accepted modules pay nothing.

## What this issue would change

- **Dependency edges per declaration** (which earlier bindings a declaration's elaboration and kernel check touched — the cache's Merkle prefix already knows the interface-level edges; the kernel check's unfolding set is the missing half).
- **Transitive rollback**: on a rejection, un-commit the failed declaration and every dependent, re-raise the dependents' diagnostics as "unknown name"/whatever the serial elaborator would have said, and keep the rest — restoring recovery mode's "report every bad declaration, keep checking the good ones" without a full replay.
- **Cache vouching by cone**: `accepted` only for declarations whose transitive dependencies all passed, recorded at join.
- **Deterministic diagnostics** must still hold: the error set and order may not depend on which verdict landed first. Sorting by declaration index at the join is the easy half; the hard half is that which *dependents* got elaborated before the abort is a scheduling race, so their diagnostics must be derivable from the dependency graph, not from what happened to run.

## When it is worth it

Only if failing-module latency in the dev loop matters: today's failure cost is one serial run plus a bounded prefix. Trigger: a measured dev-loop workload where the serial replay is the dominant wait. Until then the replay stays.

## What it assumes from elsewhere

- **[[parallel-kernel-gate]]** owns the pool, the checkpoint (`module_pass_checkpoint`/`restore_module_pass`), the early abort, and the drop guard on the pool. Assumed here: those are the primitives this would build on, and the width-independence contract is the invariant to preserve.
- **[[parallel-checking-and-caching]]** owns the verified-invalidation theorem; the cone rule here is its in-process instance.

## Log

- 2026-09-11: 2026-09-11: since §5.2 verdict reuse landed, a failing module's remaining duplicated cost is the frontend replay itself (elaboration of every declaration up to the failure, plus check_type at every gate site) — the kernel is asked once per obligation at any width. That duplicated elaboration is the datum this issue's trigger should watch: heather-cli certificate unit tests, W=8 warm, 139 s CPU against a 146 s serial gate, so today the replay is already net cheaper than serial and the trigger is not near.
