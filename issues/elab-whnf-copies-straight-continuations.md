---
title: Elaborator whnf respells structured formers by substitution: Straight's continuations
status: open
labels: [elaboration,performance,native]
area: heather-in-heather
created: 2026-10-10
updated: 2026-10-21
---

`Straight(…)(vars, state)` (`lib/elf64_straight.hthr`,
`docs/archive/native-straight-runs-design.md`) is the first workload to show the
residual [[elaborator-whnf-probes-on-computing-types]] named and left: a
former *with* sub-structure, reached only after computation, is spelled by
the substitution reducer (`reduce::whnf_type_delta`) after the value probe
has already found it.

A caller checks one term against a `Straight` type: an `Exists(q, ⟨…⟩)` per
load or store, a pair per JCC, a λ per leaf. Each anonymous constructor and
each λ asks `SemanticOracle::whnf_type` for the expected type's head. The
probe finds an `Exists`/Σ/Π and the reducer then unfolds `straight_run` →
`straight_item` → the item's arm → `SlotThen`/`StraightLeaf` by substitution,
copying the continuation (which carries every later item) at each step.

Measured once on `loop_last` (`--only`, callgrind, cached prefix): of the
elaborator's whnf time, the value probe is a few percent and
`whnf_type_delta` the rest. The callers are `prepare_ctor` and
`anonymous_ctor_expected` (a handful of calls, each expensive) and the
elaborator-side `Tc::app_at_spine` (many cheap ones). Across the five moved
command phases the elaborator's whnf is now most of each phase's time, more
than the kernel gate; it grows with the stretch's length and the proof's
nesting.

Library-side spellings tried and not enough: splitting `straight_item`'s
arms into functions (no change); spelling jump leaves by the jump's own label
(dearer). Stating the jump landing in the stretch's own spelling
(`cmd_lands`) did help and is in.

## Levers

- **Read back the head layer from the value.** The probe already holds the
  former; reading back its top constructor with its fields as closures
  instantiated to syntax (not a full normal form) would skip the reducer for
  every structured former. The audit `docs/nbe-conversion-design.md` §7 asks
  for applies: some callers anchor on spellings.
- **Memoize per checking path.** The same expected type is re-probed as the
  checker descends into a constructor's fields; a pointer-keyed memo bounds
  repeats, not the first unfolding.
- **Keep the elaborator out of it.** A form that checks a caller's proof of
  a computed type in the kernel only (as `refl` already is), elaborating its
  pieces against the unfolded type the kernel produced.

Acceptance: `loop_last`, `operand_head` and `open_back` elaborate in less
time than their kernel gate, cold, with the same kernel step counts.

## What it assumes from elsewhere

- **[[native-symbolic-execution-step]]** owns `Straight` and its callers.
  Assumed here: only that the caller's term is nested anonymous constructors
  and λs checked against an unfolding computed type.
- **[[elaborator-whnf-probes-on-computing-types]]** (closed) owns the
  probe/spell split in `SemanticOracle::whnf_type`. Assumed here: that split
  as it landed.

## Log

- 2026-10-15: **More workloads** ([[native-runs-remaining]]): `name_scan`, `read_failed`, `dash_ahead`, `loop_cursor`, `dash_test` and `name_send` in `lib/elf64_command.hthr` are each a few short stretches, and each now spends seconds in the elaborator's weak-head reducer where its hand-threaded proof spent milliseconds; together they are the command module's largest elaboration cost.
- 2026-10-16: **Lever 1 landed: the head layer is read back from the value** (`crates/elab/src/readback.rs`, wired into `SemanticOracle::whnf_type`'s structured-former branch). Profile first: on `loop_last` the elaborator's whnf time was the reducer spelling formers the value probe had already found, and its cost per step was substitution over an encoded `match` (`straight_run`'s `elim_Wf` over `Prog`, then `straight_item`'s ten-arm `case`) whose every arm spells `Asm`'s whole encoding, copied once per β and once per `case` step. The readback reads the former's top layer off the `VTy` and each child as its closure's syntax with the environment substituted in (`apply_local` through placeholder binders), never forcing anything; environment entries are memoized by identity, and only the entries the body's free indices reach are read back (`subst::local_bound`, a new public view of the bounds memo). The computed values the machine holds instead of syntax are spelled as the reducer's β spells them: a literal's predecessor (`NatRun` over `0` → `NatLit`), `elim_Nat`'s pending ih, `elim_Wf`'s `WfIh` (the reducer's λ around `nth`), and neutral spines over those; anything else declines and the reducer spells as before. **The result is the reducer's reduct node for node**: a whole-library sweep (every `lib/` module but the `certgen_code` fragment, plus `lib/std` and the x86 library, fresh cache) compared the two on every readback, about 31k of them, with zero mismatches and zero declines. Debug builds keep that comparison, sampled at the kernel's slow-check rate (`readback::verify`), because the elaborator anchors on spellings. `docs/nbe-conversion-design.md` §7 records why this does not breach its invariant (no forcing, no normal forms: the output is a reduct the elaborator already handled). MEASURED (`scripts/perf ab`, cold `lib/elf64_command.hthr` with its dependencies, width 1, 3 interleaved samples, box loaded so seconds are indicative): every counter identical except the elaborator-side `delta_body_rescopes` (fewer) and `shift_global_nodes` (+2 %, closure bodies read at a global offset); kernel steps unchanged; whole-run total −7.8 % (separate). Per item, `elab_whnf_ns` falls 70–82 % on `open_back`, `operand_head`, `read_failed`, `name_scan`, and below the kernel gate on all ten moved phases. **Acceptance, partly met**: elaboration (total − gate) is now below the gate for `open_back` and at or slightly above it for `loop_last` and `operand_head` (it was three to four times the gate). What remains of the whnf column is the readback's payload shifting under binders (`apply_local` shifts each substituted entry per occurrence) and the per-call value evaluation in a fresh arena; the rest of elaboration is not whnf. Left open for that residue.
- 2026-10-21: Straight (lib/elf64_straight.hthr), this issue's workload, was burned in B1 ([[native-burn-process-stack]]; last at 189659d, tag native-v0). The residual stays open: [[native-one-wp]]'s computed Wp is the same shape (a structural former whose continuations whnf respells) and is expected to show it again; re-measure there.
- 2026-10-21: **Re-measured on `Wp`** ([[native-one-wp]], `--only --timings` over the two loop controls of `crates/elab/tests/linux_wp.rs`, cached prefix, width 8). It shows again, and only where a syscall is: `drain_pass` (the I/O loop's pass: a read whose three answer branches each check against the continuation over `linux_answered`'s state) spends most of its time in `elab_whnf_ns`, several times its kernel gate; `count_pass` (the pure loop's pass, seven items over the frame view, no syscall) elaborates in about its gate's time. So the view record and the extra continuation arguments are not the cost (no monomorphic split, design §6.4); the answered state copied into each branch's continuation is. `drain_pass` is this issue's workload now, and the cost is felt in the suite: its test (`linux_wp.rs`) takes most of a test process's CPU rail alone, so the pure loop's tests live in a file of their own.
- 2026-11-05: gardener: cites a file it shares with [[elab-emits-normal-form-of-matched-type-argument]] (`docs/nbe-conversion-design.md`); [[refusal-tests-pin-their-reason]] (`crates/elab/tests/linux_wp.rs`).
