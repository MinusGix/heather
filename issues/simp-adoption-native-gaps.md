---
title: What simp lacked on the native proof chains
status: open
labels: [tactics,simp,native]
area: tactics
created: 2026-11-12
updated: 2026-11-12
---

The simp adoption round (2026-11-12, Minus chose it over more features)
converted chains in `lib/native/runtime/rt_loop.hthr` to `simp_only`:
`Tm::moves_to_words` (frame lemma, `set_here`, the induction hypothesis
and `words_agree` in one call, its premise discharged from a local),
`Tm::lower_leaf_sound`'s `at_n0` (`set_other`, the frame lemma and
`set_here`, unapplied, premises from locals) and
`Tm::lower_again_sound`'s `moved`. Fixed on the way: a computed
constructor's fields (a `sup_f`'s label payload) were not contracted, so
the computed goal was unspellable; and a definition named among the laws
is now unfolded (docs/simp-design.md §14). Naming a matched (non-recursive)
arm's children by their patterns as well was tried and reverted: it
changed what `omega` read in `CReal::archimedean`.

What stopped a whole proof from being one call, and what became of it:

1. ~~**A definition whose body is a match on a non-constructor**~~ (fixed
   2026-11-12, second pass): such a body unfolds when its scrutinee spells,
   the laws rewrite the scrutinee, and the match selects its arm; a
   comparison of two closed words computes. `Tm::lower_leaf_sound`'s and
   `Tm::lower_again_sound`'s final chains are one call each.
2. ~~**Fields of a literal constructor as raw projections**~~ (fixed): a
   matched arm that does not spell is contracted to the fields written.
3. ~~**Arm goals spelling a pattern's child raw**~~ (fixed): the display
   reads a projection the child's `nth` alias computes to as the pattern's
   name.
4. Papercut: `let x: a ≠ b = …` is a parse error (`expected =, found Ne`);
   `let x: (a ≠ b) = …` works.

A default set for `Valuation` (`Valuation()` is a function returning a type,
so `name_of` may not key it) is not tried yet.


Second pass (2026-11-12): also converted `Fun::fuel_zero_sound`,
`Fun::meas_zero_sound` and `Fun::meas_pass_sound` (whole final chains) and
`Fun::fuel_pass_sound`'s four Valuation lets (side conditions by
`discharge := omega(…)`), which needed laws inside a stuck match's arms,
β under a function literal, an equation's step chaining as `=` at any
carrier, and `Tm::leave_pointwise` (docs/simp-design.md §14.1).

Still open:

5. **A law whose left side has a variable head** (`left: (v) →
   finish(LoopEnd(words_of(v, ns), False)) = …`) is not matched where it
   sits in a match's arm; the proof passes it applied (`left(pv2)`).
6. **A side condition from list membership** (`id ≠ n` from `Mem(id, ns)`
   and `absent(n, ns)`, as `words_agree`'s pointwise premise needs) has no
   discharger, so `nexts_same`-style lets stay hand chains.
7. **`Fun::fuel_pass_sound`'s final chain** stays: the pass's `Sub` node's
   value computes through width casts that the proof's own `pred` does not
   have, so the computed valuation is not the proof's `pv1`.

Not tried yet: the rest of the Valuation sites (`native_structured_meaning`,
`native_compile_nodes`, `rt_lower`, `function_ir_pass`).
