---
title: Field reads still on the inline walk after per-instantiation projection names: dependent telescoped spines, non-local receivers, closed non-dependent records
status: open
labels: [elaboration,representation,performance]
area: language
created: 2026-09-10
updated: 2026-09-14
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
2. **Non-local receivers, *and* bare binders.** The reference is minted only
   where the receiver bottoms out in a local **and is not the bare local
   itself** (`receiver_admits_reference`, `crates/elab/src/inductive.rs`;
   narrowed 2026-09-13 by [[x86-scaling-rail-out-of-fuel]], which found the
   one-sided version disagreeing with itself under substitution). A projection
   reference is cheap to compare and dear to compute through
   (`caller_native_memory_same_28` needed 8–64× `DEFAULT_FUEL` with it,
   §13.10, re-confirmed on the 2026-09-13 tree). Not separated from 1 in the
   counts; `stack_word_agrees` and `stack_word_matches` are the two remaining
   `Sigma`/`El(?)` payers, and every bare-local read now joins them.
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

- 2026-09-11: Merged in [[setoid-dictionary-projection-growth]] as a second customer (2026-09-11): large dependent setoid dictionaries (docs/showcase/finite_set_client.hthr, derive_set_function_clients.hthr; flat client exhausted 4 GiB, tagged parent died at ~283 s, indexed layout checks in ~4 s) are the dependent-telescoped-spine family of item 1. That file stays as the reproducer.
- 2026-09-13: 2026-09-13: a fourth customer, and the second boundary failing on its own terms — the 20-node x86 rail's artifact theorem computes through the MachineState<M> projection reference over a 22-instruction symbolic execution (receiver rooted in the local before, so the reference IS minted) and exhausts both fuel and depth; passed before 9ae0855. Bisect and numbers on [[x86-scaling-rail-out-of-fuel]]. The trigger fired.
- 2026-09-13: Boundary 2 narrowed, and it was failing on *both* sides. [[x86-scaling-rail-out-of-fuel]] shows it was one-sided — the reference is minted at a local, so a record's field type carries one, and the moment a constructor substitutes a computed state into that binder the same boundary declines at every statement written against it. The gate is now `receiver_admits_reference`: neutral **and not a bare `Var`**. What that leaves unnamed is one entry longer and one entry shorter: every bare-local field read is back on the inline walk (+19,984 misses / +1.8 s kernel on the reused_callee certificate, `stack_word_agrees` the clearest case — the residual payer this issue already named), and computed receivers are unchanged. **Follow-up worth a slice**: decline at a bare local only inside a declaration's *stated* type, where substitution can happen, and keep the reference in term position — that is where most of the 3 % went. Widening to every receiver and to one layer of computation were both re-measured on the 2026-09-13 tree and both re-broke `caller_native_memory_same_27/28`.
- 2026-09-13: Coordinator review of the 2026-09-13 narrowing: the bare-binder rule covers the observed customer, not the invariant. A chain rooted at a binder (v.snd.fst with v a record field or parameter that a constructor later substitutes by a computed value) flips from a minted reference to a declined walk under the same substitution, so a declaration whose field type reads a chain off an earlier field is the next twin waiting for a customer. Kept the chain minted because it is §13.1's measured payer; if that twin appears, the stated-type/term-position split in the follow-up above is the shape that fixes both at once.


- 2026-09-15: **Boundary 1 is closed by the dependent telescoped device** (`docs/telescoped-record-projections-design.md`, implemented 2026-09-15). `register_rec_projs` now chooses by the *dependency* test and wraps by the *telescope* test independently: a dependent spine gets the closed `RecFam`/`RecProj`/`RecTail` triple with the declaration's own `Θ` in front, a non-dependent telescoped one keeps the simple `λΘ.λv. fst(sndʲ v)`, and the one declined cell is the closed non-dependent record (§13.6's own omission, untouched). `CollectionLiteral<A>(n)`, `Monoid<A>` and every record in `lib/std/parser` therefore register. Boundary 2 (`receiver_admits_reference`) is *narrowed* rather than closed: the dependent device is exempt from it at every receiver, exactly as the closed device is, because there the alternative to the reference is the tail-substitution exponent rather than a linear walk — the non-dependent telescoped cell keeps the gate verbatim and `caller_native_memory_same_27/28` with it. Boundary 3 is untouched. Two prerequisites landed with it and have reach well beyond records: the stored `TyCodeFn` is read through a rescoping and a frame-correct substitution ([[type-code-fn-template-stale]]), and the hole matcher descends into `App`/`Fst`/`Snd` and recovers every hole as a **code**. Numbers on [[parser-certified-composition-cost]]. The issue stays open for boundaries 2 and 3.

### 2026-09-14 — substitution-chain regression coverage

`crates/elab/tests/annotation_cost.rs` now tests a later equality field after
substituting bare and computed receivers for an earlier output field. It
varies field-chain depth 1/2/3 and rebuilding steps 0/1/2/4/8, with open-type
checking, literal computation and false-equality controls. These cases pass
with modest evaluator-step growth; the measurement table lives in
[[call-run-checked-theorem-cost]]. No receiver-policy change follows from
this bounded probe, and the larger native scaling workloads remain required.
- 2026-11-05: gardener: cites a file it shares with [[relational-algebra-normalization]] (`docs/showcase/finite_set_client.hthr`); [[setoid-auto-lifting]] (`docs/showcase/finite_set_client.hthr`).
