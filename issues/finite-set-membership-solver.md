---
title: Decide membership goals over finite-set expressions
status: closed
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

## Log

- 2026-11-09: Built. `lib/std/data/set/set_solve.hthr` reflects set expressions (atoms, `Cons` of an indexed element, a filter by an indexed predicate, and registered binary operations whose `SetLaw` names their connective: ∪, ∩, ∖) into Booleans of the leaves, proves the reading sound (`SetExpr::reflects`), and `set_solve` turns a closed `set_taut(…) = True` (by `refl`) plus the facts' proofs into the goal. `lib/std/data/set/set_ops.hthr` is the operation registry (`SetOpEntry`, `++` registered); `lib/std/tactic/set_tactic.hthr` is `sets()`: it reads `Mem`/`¬Mem`/`¬(x = e)`/inclusion hypotheses at the goal's element (an inclusion is applied to it, so `Inside` and any `(i) → Mem(i, a) → Mem(i, b)` count), introduces inclusion goals, reads `False` goals at a membership's element, reads an unknown call through its definition when that is a call again (`live_before` as `union`), adds `x ∈ [e]` for elements convertible to `x`, runs the table in Heather first and refuses with the falsifying assignment, one note per leaf. Native registers `union` (∪) and `minus` (∖) with their laws in `native_alloc`; `inside_union`, `inside_minus`, `inside_live_before` (native_alloc) and `live_before_keeps`, `live_before_reads` (native_compile_homes) are now `by sets()`. Probes and the negative control: `lib/_tests/std/tactic/set_tactic_tests.hthr`. Boolean spellings (`absent`, `holds`, `within`), `DecEq<Gpr>` and migrating the remaining chains: [[set-solver-boolean-spellings]].
