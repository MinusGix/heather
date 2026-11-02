---
title: Group the Elaborator's fields by lifetime (module pass, dynamic scope, policy, memos)
status: open
labels: [elaboration,refactor,state-machine]
area: infrastructure
created: 2026-11-02
updated: 2026-11-02
---

Group the `Elaborator`'s fields by lifetime so each group has one clone rule and one rollback rule, instead of encoding lifetimes in custom `Clone` impls and hand-kept exception and reset lists.

## Problem

`Elaborator` (`crates/elab/src/lib.rs` ~610–815) carries ~60 fields in six lifetime classes the type does not name: committed world, module pass, declaration attempt, dynamic scope, policy, memos (table in `docs/implicit-state-machines-survey.md` §1). The classes are enforced by convention across three custom `Clone` impls (`KernelPool`, `ReplaySlot`, `JournalSlot`), the exception list in `restore_from_clone`, the reset list in `restore_module_pass`, the memo clears in `SessionCheckpoint::restore` and again in the slice replay (`module_delta.rs` ~1009), and `fork`/`fork_over`/`SemanticImage::elaborator`.

This has already produced a defect: whole-elaborator undo (`*self = snapshot`) assigned a clone's inline, empty pool over the live one, silently dropping queued verdicts and leaving the gate inline for the rest of the module (`pool.rs` ~596). It is now caught only by a `debug_assert!` in `KernelPool::drop` and by callers remembering to use `restore_from_clone`. The next module-pass field, or the next Ψ-position-keyed memo, falls into the same hole unless someone adds it to the right lists; nothing fails to compile.

## Proposal

- Sub-structs named by lifetime: `ModulePass` (pool, replay, journal, slice plan, container decls/at, warnings, omega reports, pending derived), `DynamicScope` (the ~15 save/restore fields), `Policy`, `Memos`, beside the existing `CommittedWorld` and `DeclAttempt`.
- One clone rule and one rollback rule per group. `restore_from_clone` becomes "restore everything except `ModulePass`"; `Memos` has one `clear_positional()` called by every rollback.
- `DynamicScope` gets a `scoped(&field, value, |me| …)` helper (the `generated_mode` shape, `access.rs` ~183), so restoring the *outer* value is the default. Three sites today reset instead of restoring (`impl_provenance = None`, `misplaced_recursion = None`, `meta_pushed.clear()`), which is wrong only if the extent nests (survey §8).
- While there: the elaborator holds "under a quotation" twice (`Cx::quoted` and `quote_depth`) because helpers that start from a fresh `Cx` lost the first (survey §7). Decide one home.

Mechanical, no behaviour change; the gain is that a new field must pick a group. Overlaps the data-oriented design survey's regrouping of the same struct; do them together or let one land first.

## What it assumes from elsewhere

- **[[parallel-kernel-gate]]** owns the pool and the width-independence contract. Assumed here: only that the pool and replay are module-pass state, never restored by a declaration rollback.

## Related

Filed together from the implicit-state-machines survey (`docs/implicit-state-machines-survey.md`, 2026-11-02, ranked there): [[module-pass-state-machine]], [[kernel-psi-bound-cache]], [[decl-attempt-lifecycle]], [[goal-slot-state-enum]], [[kernel-checker-mode-enum]].
