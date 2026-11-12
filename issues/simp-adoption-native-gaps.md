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

What still stopped a whole proof from being one call:

1. **A definition whose body is a match on a non-constructor** (`Tm::leave`
   matches on `after(64, flag).eq_bit(1)`) cannot be unfolded: the match
   is not spelled, so the unfolding is refused. What is wanted is to rewrite
   the scrutinee (`set_here` makes it `ofNat(1).eq_bit(ofNat(1))`), let the
   match compute, and only then show the arm. Today the proof keeps a
   `cong_fn` over the match.
2. **Unfolding a function that reads a constructor's fields at a literal
   constructor** (`Node::step(Const(64, flag, 1), v)`) leaves the fields as
   projections of the label payload (`ofNat(fst(snd(…)))`), not the
   literal's arguments.
3. **Arm goals spell a pattern's child as the raw children projection**
   (`leave_region(l, flag, n0, fst(cs))` for `rest`) in the goal the
   elaborator hands an arm reached through `Option::and_then_elim`, so a
   law over `rest` cannot be spelled there. This is the elaborator's goal,
   not simp's computation.
4. Papercut: `let x: a ≠ b = …` is a parse error (`expected =, found Ne`);
   `let x: (a ≠ b) = …` works.

Not tried yet: a default set for `Valuation` (`Valuation()` is a function
returning a type, so `name_of` may not key it), and the rest of the
Valuation sites (`native_structured_meaning`, `native_compile_nodes`,
`rt_lower`, `function_ir_pass`).

## Log

- 2026-11-12: Three theorems of `lib/native/runtime/rt_loop.hthr` that #577 converted to `simp_only` went back to their written chains when PR #551 merged master: their statements there are over a file (`Fun::GuardedBy`), and the converted proofs are of the statements without one. Converting them again over the new statements is the small piece left here from that merge; the chains are the same shape, with the file as one more fixed argument.
