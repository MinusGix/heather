---
title: Group the Elaborator's fields by lifetime (module pass, dynamic scope, policy, memos)
status: closed
labels: [elaboration,refactor,state-machine]
area: infrastructure
created: 2026-11-02
updated: 2026-11-02
---

Group the `Elaborator`'s fields by lifetime so each group has one clone rule and one rollback rule, instead of encoding lifetimes in custom `Clone` impls and hand-kept exception and reset lists.

## Problem

`Elaborator` (`crates/elab/src/lib.rs` ~610–815) carries ~60 fields in six lifetime classes the type does not name: committed world, module pass, declaration attempt, dynamic scope, policy, memos (table in `docs/elaborator/implicit-state-machines-survey.md` §1). The classes are enforced by convention across three custom `Clone` impls (`KernelPool`, `ReplaySlot`, `JournalSlot`), the exception list in `restore_from_clone`, the reset list in `restore_module_pass`, the memo clears in `SessionCheckpoint::restore` and again in the slice replay (`module_delta.rs` ~1009), and `fork`/`fork_over`/`SemanticImage::elaborator`.

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

Filed together from the implicit-state-machines survey (`docs/elaborator/implicit-state-machines-survey.md`, 2026-11-02, ranked there): [[module-pass-state-machine]], [[kernel-psi-bound-cache]], [[decl-attempt-lifecycle]], [[goal-slot-state-enum]], [[kernel-checker-mode-enum]].

## Log

- 2026-11-02 — DONE. The flat fields are five groups beside the committed
  world, in `crates/elab/src/lifetimes.rs` (the module doc carries the
  clone/rollback table): `ModulePass` (pool, replay, journal, slice plan,
  container decls/at, warnings, both omega report lists, pending derived,
  unfold refusals, export proofs), `DeclAttempt` (unchanged),
  `DynamicScope` (the extent fields, including the survey's
  declaration-extent four: `member_owner`, `misplaced_recursion`,
  `instance_scope`, `impl_provenance`, whose rule is the dynamic scope's,
  not `prepare`/`finish`'s), `Policy`, `Memos`.
  - `restore_from_clone` destructures the snapshot and restores every
    group but the module pass; `ModulePass::roll_back_to` decides field by
    field (pool and replay stay live, journal cut to the snapshot's lengths,
    the rest the snapshot's — exactly the old behaviour). `ModulePass`'s
    `Clone` names every field, and `KernelPool`/`ReplaySlot` are no longer
    `Clone` (`JournalSlot`'s clone is `lengths_only`), so the clone rule has
    one home. A new field in either does not compile until it picks a rule.
  - `Memos::clear_positional` (names every memo) replaces the three copies
    of the two clears (`SessionCheckpoint::restore`, both slice replays).
  - `Elaborator::scoped` / `scoped_cell` restore the outer value; the
    hand-restored sites and the three resetting ones (`impl_provenance`,
    `misplaced_recursion`, `meta_pushed` at the end of a `meta fn`) use
    them. Left on their own guards: the depth counters with guards already,
    `resolve_depth` (absolute sets), `instance_scope` (a block that
    accumulates, cleared by its block and by `restore_module_pass`).
  - "Under a quotation" has one home, `DynamicScope::quote_depth`
    (`Elaborator::under_quotation`); `Cx::quoted` is gone. Only behavioural
    edge: the named-type memo now skips a fresh `Cx` inside a payload too.
  - Not done here, owned elsewhere: the module-pass checkpoint's own reset
    list (`restore_module_pass`) is [[module-pass-state-machine]]'s; the
    `DeclAttempt` field lists are [[decl-attempt-lifecycle]]'s.
