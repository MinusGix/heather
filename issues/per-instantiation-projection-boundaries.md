---
title: Field reads still on the inline walk after per-instantiation projection names: dependent telescoped spines, non-local receivers, closed non-dependent records
status: open
labels: [elaboration,representation,performance]
created: 2026-09-10
updated: 2026-09-10
---
The three boundaries docs/per-instantiation-type-codes-design.md §13.9
measured into place (2026-09-10), each leaving a family of field reads on
`project_field`'s inline `fst(sndʲ v)` walk, where the kernel's `Fst`/`Snd`
rule reconstitutes `Σ(fst_ty). snd_ty` and converts it against the receiver's
(named) type — the `Sigma`/`El(?)` and `Sigma`/`El^δ` rows of the conv-miss
table on `build-x86 mix` (2,651 / 8.0 s and 6,247 / 5.8 s after the round;
counts are the datum, seconds one box):

1. **Dependent telescoped spines** (`CollectionLiteral<A>(n)`, 166 reads on
   that run; `Monoid<A>`). The simple telescoped definition
   `λΘ.λv. fst(sndʲ v)` would write the tail out — the exponent the closed
   device's `RecTail`/`RecFam` companions exist to remove — so the gate
   declines them (§13.3). Fix shape: the closed triple abstracted over the
   telescope, gated by the same dependency test.
2. **Non-local receivers.** The reference is minted only where the receiver
   bottoms out in a local (`receiver_is_neutral`, `crates/elab/src/inductive.rs`);
   a projection reference is cheap to compare and dear to compute through
   (`caller_native_memory_same_28` needed 8–64× `DEFAULT_FUEL` with it,
   §13.10). Not separated from 1 in the counts; `stack_word_agrees` and
   `stack_word_matches` are the two remaining `Sigma`/`El(?)` payers.
3. **Closed non-dependent records** (`InstructionBytes`, `Region`,
   `ConditionalJoinRegion`, `LinkedConditionalBlock`): the closed device's own
   dependency gate, §13.6 — a different boundary with a different argument (a
   closed receiver's type is `El (D#tycode^δ)` while the device's domain is
   the inline `⟦D⟧`).

## When

Triggered: the next time `Sigma`/`El(?)` or `Sigma`/`El^δ` is a top row on a
measured workload — one deliberate round. Re-take the attribution first
(§13.1's method: a decline trace in `project_field`, by declaration and by
receiver shape); a silent decline looks exactly like a device that fired and
lost.

## What it assumes from elsewhere

- **[[per-instantiation-type-codes]]** owns the mechanism and the numbers
  above. Assumed here: only the three boundaries as landed.
- **[[theorem-field-projection-oom]]** owns the closed device. Assumed here:
  only its dependency gate and its tail/fam companions.

## Log
