---
title: Recast the x86 states-equal-except-AF relation as a setoid
status: closed
labels: [native,x86,setoids,relations,proofs]
created: 2026-10-10
updated: 2026-10-13
---

The native-side setoid client chosen on 2026-10-10, to start after
[[native-straight-code-triples]] lands (the instruction-stepping thread owns
`lib/elf64_*` and the register frame relations until then).

`SameDefinedState<M>` (`lib/std/arch/x86_64/x86_64.hthr`, "states equal except
AF") is a textbook setoid. It is the pullback of `=` along `erase_af`. Today:

- refl, sym and trans are each written out field by field over 8 fields
  (`same_defined_refl/_of_equal/_sym/_trans`);
- `same_defined_erased_equal` and `erased_equal_same_defined` cross to and
  from the erased state through `trans(cong_fn(λ … MachineState(…)))` chains;
- about 20 `*_respects_defined` / congruence lemmas spread over `x86_64.hthr`,
  `x86_64_block`, `x86_64_data_read`, `x86_64_fetched_code`,
  `x86_64_step_forms` and `x86_64_store` follow one pattern: erase, commute,
  `cong_fn`, `trans`, `sym`. `respects_by_erasing`
  (`linux_x86_64_determinism.hthr`) is the generic "commutes with the
  quotient map, so respects the relation" lemma, written once for one case.

Do: state `SameDefinedState` as `relation_props::Pullback(erase_af, =)` (or
prove it equivalent), take its `Equivalence` from `pullback_equivalence`, and
replace the per-function congruence lemmas by one generic
"respects-by-erasing" lemma plus registered instances so `rel_cong` can use
them. Then check whether `SameResponse`/`SameResponses` in
`linux_x86_64_determinism.hthr` fit the same way.

Acceptance: the hand-written equivalence and congruence lemmas gone or reduced
to one-line instances, with every native gate's certificate cost no dearer
(these files are in every native build's prefix, so measure with the counters,
not seconds).

## What it assumes from elsewhere

- **[[native-straight-code-triples]]** owns the register/slot frame relations
  (`Keeps`, `SlotsKeep`). Assumed here: only that it does not change
  `SameDefinedState`.

## Log

- 2026-10-13: **Landed.** `SameDefinedState<M>(left, right)` is now `erase_af(left) = erase_af(right)`, a `fn` rather than an eight-field record, and `SameDefinedState::pullback` shows by `refl` that it is `Pullback(erase_af, RelId)`.

  - **Equivalence.** `instance<M> Equivalence<MachineState<M>>(SameDefinedState<M>)` takes its three fields from `pullback_equivalence(erase_af, RelId, relid_equivalence())`. `designation ≈ at MachineState` lets proofs write `≈` and use `calc`. The hand-written `same_defined_refl`, `_of_equal`, `_sym` and `_trans`, `erased_flags_equal`, `same_defined_erased_equal` and `erased_equal_same_defined` are all gone. Callers now write `refl`, `sym`, `trans` and `SameDefinedState::of_equal`. The defined components are read back by `SameDefinedState::gprs`, `::rip` and `::memory`. A `self` receiver (`same.memory()`) does not resolve on a `fn`-typed proposition, so these are called by name.
  - **Congruence.** `same_defined_respects(f, commute)` (moved from `respects_by_erasing` in the determinism module) gives `PreservesRelation(SameDefinedState, SameDefinedState, f)` whenever `f` commutes with `erase_af`. Every per-function lemma is now one application of it, registered as an `evidence theorem`, so `rel_cong` finds it: `execute_normal`, short and near control, the byte and word load results, and the store result. The load, store, control and canonical-execute chains are `calc { … ≈ … }` with `rel_cong` for the step through the instruction. `x86_64` now imports `relation_props`, which is added to the native support bundle and the test bundles that carry `x86_64`.
  - **`SameResponse`/`SameResponses`: left as they are.** `SameResponse` is the pullback of `=` along an event's kind and result. Recasting it would need a response type with six constructors. Every consumer would then trade the current reduction to `result = other` for an injectivity proof. `SameResponses` is also named in the generated read-loop certificates (`crates/cli/src/native/read_loop.rs`), so its shape is part of what native gates check.
  - **Cost** (`heather check --timings` of `linux_x86_64_determinism` and its imports, cold, against master): about 1.5% fewer kernel steps and 2.7% fewer conversion misses overall. Steps fell in every touched module except `x86_64_data_read`, plus the newly imported `relation_props`, which is small. The `calc`/`rel_cong` chains are dearer than the `trans` chains they replace, by far more than the terms warrant. The relation's lemmas shrank by more, so the total still drops. That cost is filed as [[setoid-surface-kernel-cost]]. No certificate changes shape: nothing the native generators emit names a deleted lemma.
  - Tests: `crates/elab/tests/x86_64.rs` (`same_defined_setoid_check`) checks two nested steps by `rel_cong`, TEST's two results through one more step, and a generic `Equivalence` lemma resolved at `SameDefinedState`. It has three controls: a function that branches on AF has no `refl` commute proof, `rel_cong` through it leaves `?compatibility`, and TEST's two results are not `=`.
