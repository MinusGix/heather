---
title: Recast the x86 states-equal-except-AF relation as a setoid
status: open
labels: [native,x86,setoids,relations,proofs]
created: 2026-10-10
updated: 2026-10-10
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
