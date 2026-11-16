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

Review: `docs/kernel/kernel-implicit-state-review.md` §1.

## Proposal

1. Bind the arena to its `Defs`: `ValueArena::new(defs)`, `Eval::new(fuel, base, &arena)`, and an `extend` that asserts the new Ψ extends the old. Mechanical. Also touches `crates/elab/src/host.rs`, `sealing.rs`, `readback.rs`.
2. Remove the mode dependence: measure always forcing `n.unfold` thunks transparently, so a glued unfolding's memoized value is the same whoever asks first. If that costs the δ-lazy stage too much, record a mode bit per memo entry instead, and have a transparent reader treat an opaque entry as a miss.

Completeness and determinism, not soundness: a transparent value is δ-equal to the opaque one. Kernel hot path, so use `scripts/bench --check`, the conversion benchmarks, and `scripts/perf ab` on the library gate.

## Related

[[kernel-premise-queue-type]], [[kernel-psi-bound-cache]] (the same "cache bound to its Ψ" shape one level up), [[elaboration-determinism]].

## Log

- 2026-11-08: first attempt, not landed (`docs/kernel/kernel-implicit-state-review.md` §1 has the details; patches in `/mnt/project-files/value-memo-unfolding/`). Reproduced by reverting #459's look-ahead: 5 `NotConvertible` in `interval_tactic_tests`. A level tag on memo entries, with transparent readers rejecting lazy values, fixes them at under 1% cost on calc_parser (shared-application memo left untagged). But it makes `creal_tests::half_terms` and `rt_lower_tests::spread_agrees` run out of fuel, because re-evaluating loses the lazy run's sharing. Resuming stuck spines instead keeps those passing but does not fix the 5. The level belongs to values (`TmClo::Val`, conversion's `wa`/`wb` handed between stages), not to memo entries. Next: find the exact #459 path; or give `Val` a level byte.
- 2026-11-08: the exact #459 path found and fixed narrowly (`docs/kernel/kernel-implicit-state-review.md` §1, second attempt). A withheld (`interface fn`) call is glued only at closed arguments, and closedness was decided by forcing in the run's mode: a δ-lazy force leaves a closed argument as an eliminator stuck on a glued scrutinee, which the walk called open, so the call was memoized unglued and the transparent run could not unfold it. `Eval::closed` now forces transparently and walks into such a glued neutral's unfolding; regression test `a_withheld_call_at_a_lazily_stuck_closed_argument_is_glued`. The five interval verdicts pass under the lazy look-ahead too, but #459's transparent look-ahead stays (the lazy one runs `spread_agrees` out of fuel). Still open: proposal 1 (bind the arena to its `Defs`), and the memo's general mode-blindness, which is now a cost question with no known refusal.
