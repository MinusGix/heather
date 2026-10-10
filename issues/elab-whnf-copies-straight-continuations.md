---
title: Elaborator whnf respells structured formers by substitution: Straight's continuations
status: open
labels: [elaboration,performance,native]
created: 2026-10-10
updated: 2026-10-10
---

`Straight(…)(vars, state)` (`lib/elf64_straight.hthr`,
`docs/native-straight-runs-design.md`) is the first workload to show the
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
