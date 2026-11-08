---
title: Make the value memo independent of the evaluator's mode
status: open
labels: [kernel,state-machine,determinism,conversion]
area: kernel
created: 2026-11-08
updated: 2026-11-08
---

Make the value memo independent of the mode a value was first forced in, so a conversion verdict cannot depend on which query ran first.

## Problem

`ValueArena` (`crates/kernel/src/value.rs` ~295) memoizes forced closures by address (`term_cache`) and closed closures by body identity (`closed_values`). Whether a forced value is δ-transparent depends on `Eval::transparent` (`eval.rs` ~279): under it, an eliminator stuck on a glued scrutinee unfolds and retries (~2143); without it, the eliminator stays stuck. The memo records neither, so the first force decides what every later reader sees.

This already bit: #459 (`a9cb55b`) found `meet_on_the_way` forcing glued unfoldings opaquely. The transparent run that read them could not step, and conversion refused a convertible interval verdict. The fix (`Eval::delta_step_transparent`) covers that one look-ahead. The other opaque δ-steps (`Dom::delta_tm`/`delta_ty`, `conv/dom/values.rs` ~727, ~750) are safe only because no transparent run reads their thunks first.

The arena's classifications (`fold_classes`, `transducers`, `bit_types`) rest on a second unenforced pairing: "the definitions, both fixed for one arena", while `Eval::new(fuel, defs, base, &arena)` takes the two separately and conversion builds a fresh `Eval` per step (`run`, ~523). The real invariant is that Ψ only extends within one arena.

Review: `docs/kernel-implicit-state-review.md` §1.

## Proposal

1. Bind the arena to its `Defs`: `ValueArena::new(defs)`, `Eval::new(fuel, base, &arena)`, and an `extend` that asserts the new Ψ extends the old. Mechanical. Also touches `crates/elab/src/host.rs`, `sealing.rs`, `readback.rs`.
2. Remove the mode dependence: measure always forcing `n.unfold` thunks transparently, so a glued unfolding's memoized value is the same whoever asks first. If that costs the δ-lazy stage too much, record a mode bit per memo entry instead, and have a transparent reader treat an opaque entry as a miss.

Completeness and determinism, not soundness: a transparent value is δ-equal to the opaque one. Kernel hot path, so use `scripts/bench --check`, the conversion benchmarks, and `scripts/perf ab` on the library gate.

## Related

[[kernel-premise-queue-type]], [[kernel-psi-bound-cache]] (the same "cache bound to its Ψ" shape one level up), [[elaboration-determinism]].
