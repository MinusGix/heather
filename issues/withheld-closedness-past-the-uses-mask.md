---
title: A withheld call unfolds at a function argument that reads a far local variable
status: open
labels: [kernel,interfaces]
area: kernel
created: 2026-11-16
updated: 2026-11-16
---

A withheld definition is glued to its body only at a saturated call whose
arguments read no free local variable (`crates/kernel/src/eval/withheld.rs`,
`docs/language/interface-definitions-design.md` §3). A function argument is
classified without forcing its body: `binder` reads the body's mask of used
indices (`bounds::LocalUse::uses`) and forces only the environment entries
the mask names. Two things made the mask say "unused" for an index that
occurs, so the function was judged closed and the call unfolded at an open
argument:

- **The walk read four bits the mask does not have.** The mask covers
  indices below `USES_BITS` (60); the walk tested `i < 64`, and bits 60 to 63
  of what it was handed are always clear. A body reading index 60 to 63 was
  read as not reading it.
- **A binder dropped indices from past the mask into it unnamed.**
  `LocalUse::under(k)` shifted the mask right by `k`. An index at or past
  `USES_BITS` under the binder is counted by `bound` alone, so after the
  shift the indices `USES_BITS - k ..` had clear bits whether or not they
  occurred: `λ. λ. x₆₀` showed no use of its free index 59.

Not a soundness defect: gluing only ever unfolds the body ordinary δ would
(the module's own argument), and the other reader of the mask,
`bounds::ignores_innermost`, decides whether a fold's step is probed, never a
verdict. What it breaks is the interface boundary: a client's proof could
come to depend on a withheld body at an open argument. It needs a function
argument whose body sits under sixty binders of its environment, which a
long `let` chain or a generated term reaches and hand-written code rarely
does.

Found by reading, while looking for kernel soundness flaws (2026-11-16).

## Fixed: the four bits

The walk reads an index at or past `USES_BITS` as used. Regression test:
`eval_differential::a_withheld_call_at_a_function_reading_a_far_variable_stays_withheld`
(indices on both sides of the mask, under one and two binders); it fails
without the change, at index 60.

## Open: the binder's shift

`LocalUse::under` still drops an index from past the mask into it unnamed, so
the mask under-reports for a body with a reference more than sixty binders
out from where it sits. The sound repair inside the mask is to name every
index a binder brings under it, as far as the bound allows. That was tried
and costs what the mask exists to save: under sixty nested binders with a
far reference every low bit ends up set, `ignores_innermost` then answers
"read" for steps that do not read their hypothesis, and they are probed
again (`annotation_cost::valuation_lookup_case_step_cost` and
`lib_std_bitvec::valuation_lookup_dispatch_cost_does_not_follow_result_width`
both moved). Other directions, for whoever owns the head's layout:

- one more bit in the head, "the mask is not exact below here", set where a
  binder shifts a bound past `USES_BITS`; the closedness walk then forces
  every entry below the bound for such a body and the probe keeps reading
  the mask as the hint it is;
- the closedness walk stops using the mask and forces every entry below the
  bound, which judges more calls open than today.
