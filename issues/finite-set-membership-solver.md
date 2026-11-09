---
title: Decide membership goals over finite-set expressions
status: open
labels: [tactics,native,sets]
area: tactics
milestone: [hih-passes]
created: 2026-11-09
updated: 2026-11-09
---

Native proofs represent sets of identifiers as lists (`List<Nat>` with
`absent`, `holds`, `union`, `minus`, `Inside` in `lib/native/native_alloc.hthr`;
`List<Gpr>` register pools) and carry membership across them by hand. Over
`lib/native`, arch and os there are about 1,080 such citations (`Mem(` 257,
`absent(` 237, `union(` 81, `Inside(` 64, `minus(` 55, …), and `lib/native`
keeps about 30 set lemmas of its own. `grind` does not prove membership goals
(probe P4, `docs/native-mathematics-survey.md` §9). Survey rank: 1.

Membership in a set expression built from atoms by ∪, ∖, ∩, `++`, `Cons`
and a filter is a Boolean function of the atoms' memberships (the Boolean
algebra of sets is pointwise), so hypotheses ⇒ goal is a truth-table check,
and inclusion is the same check at a generic element.

## Scope

- A reflected `SetExpr` (atoms, union, difference, intersection, append,
  singleton/`Cons` with a literal element), a Boolean denotation `mem(x, e)`
  through `absent`, and its soundness against `Mem`.
- A tactic that reifies `Mem`/`Inside`/`absent(…) = True|False` goals and
  hypotheses, and closes them by a closed verdict `= True` by `refl`
  (`docs/proof-patterns.md`). Literal elements add equality atoms decided by
  the element type's decidable equality.
- Over the lists the compiler already uses: nothing migrates to `FiniteSet`.

## Done when

A liveness lemma in `native_alloc` or `native_compile_homes` that chains
`union_left`/`inside_minus`/`absent_mem` is one tactic call, and a negative
control (a goal that is not a tautology) is refused naming the atom
assignment that falsifies it.

## What it assumes from elsewhere

- **[[address-interval-sets]]** produces footprint goals of this shape once
  intervals are reduced to endpoints. Assumed here: nothing; this issue
  stands alone.
