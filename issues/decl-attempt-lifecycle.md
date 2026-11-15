---
title: Explicit declaration-attempt lifecycle: scoped attempt API, phase check, structural reset, delta_psi upkeep
status: open
labels: [elaboration,refactor,state-machine]
area: infrastructure
created: 2026-11-02
updated: 2026-11-02
---

Give the declaration attempt an explicit lifecycle: a scoped API for the attempt protocol, a phase check on `prepare`, structural reset, and `delta_psi` maintained by the operations that move it.

## Problem

An ordinary declaration's scratch state moves Idle → restartable → elaborating (possibly restarting) → frozen (`on` clauses) → finished, carried by `GoalArena`'s `restart_enabled`, `frozen`, `base`, `written_base`, `requested_base`, `promoted_seen` and by call order (`crates/elab/src/attempt.rs`, `goals.rs` ~84, `lib.rs` `elab_decl_one` ~3739). Survey: `docs/elaborator/implicit-state-machines-survey.md` §4.

- `DeclAttempt::prepare` and `finish` enumerate the fields to clear, and the lists differ on purpose (`op_fallback_uses` is read after `finish`, `direct_dependencies` before it). A new field must be placed by reading callers.
- The attempt protocol (`prepare; configure; refresh_delta_psi; …; finish; refresh_delta_psi`) is copied at `check_measure_is_nat`, `group_universe` (`mutual_rec.rs` ~567) and the two measure queries (`measure_context.rs` ~20, ~62).
- The measure queries clone the elaborator and call `prepare` + `configure(0, 0)`. `GoalArena::prepare` keeps the goal entries, so that is a fresh attempt only because the queries run between attempts. Mid-attempt, the clone would keep the outer goals over base 0.
- `delta_psi` (Ψ plus goal-base placeholders) sits in `CommittedWorld` though it depends on the attempt's base, and is refreshed by hand at 15 sites. Every Ψ push found is followed by a refresh; nothing enforces it.

## Proposal

- `with_attempt(written, reserved, |me| …)` for the protocol; the measure queries use it on their clone.
- A phase (enum, or at least a debug assertion) so `prepare` from a non-idle arena is caught.
- Reset by assigning fresh values instead of listing fields; what is read after `finish` comes back as the attempt's result.
- `delta_psi` built lazily from (Ψ identity, base), or written only by the Ψ-push and `configure` methods.

## What it assumes from elsewhere

- **[[elab-field-lifetimes-explicit]]** names `DeclAttempt` as the attempt-lifetime group. Assumed here: only that grouping, not its timing.
- **[[goal-slot-state-enum]]** is the per-slot half of the arena.

## Related

Filed together from the implicit-state-machines survey (`docs/elaborator/implicit-state-machines-survey.md`, 2026-11-02, ranked there): [[elab-field-lifetimes-explicit]], [[module-pass-state-machine]], [[kernel-psi-bound-cache]], [[goal-slot-state-enum]], [[kernel-checker-mode-enum]].
