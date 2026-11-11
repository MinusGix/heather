---
title: simp: rewrite along a law between statements (P ↔ Q)
status: closed
labels: [tactics,proofs,relations]
area: tactics
milestone: [tac-general]
created: 2026-11-11
updated: 2026-11-11
---

`simp_only` takes laws that conclude an equation `a = b` or a designated
relation `R(a, b)` between terms (`docs/simp-design.md` §5). A law `P ↔ Q`
relates two *statements*, and the relation walk
(`crates/elab/src/rewrite/relation.rs`) rewrites terms inside a goal, with
contexts that are term operations carrying `PreservesRelation`/`Respects2`
evidence. A statement's contexts are type formers (`∧`, `∨`, `→`, `¬`, a
quantifier, an applied predicate), which that walk does not cross, so such a
law is refused by name:

    theorem iff_law(P, Q: Type, h: P ↔ Q, q: Q): P { simp_only(h, then := q) }
    // `h` is not a law … a law `P ↔ Q` between statements is not rewritten yet

(`lib/_tests/std/tactic/simp_tests.hthr`, `iff_law`). The design has `↔` in
the first rounds with sets, because the facts a set wants most are of this
shape (`x ∈ xs ++ ys ↔ x ∈ xs ∨ x ∈ ys`, `a <= b ↔ …`).

Wanted: a statement walk beside the term walk. A goal's occurrence of `P`
is the whole goal, a component of a connective (`iff` congruence lemmas of
`logic`: `and_congr`, `or_congr`, `imp_congr`, `not_congr`), or the body of
a `∀`/`∃` (pointwise). The proof is `Iff` evidence for the whole goal, used
by `mpr`. Equations and relation laws that fire inside a statement's terms
already cross it by `J` or by the relation walk; this is only for laws whose
sides are statements.

Done when `iff_law` and a membership probe
(`x ∈ (xs ++ ys) ++ zs` to a disjunction by `List::mem_append`) close by
`simp_only`.

## Log

- 2026-11-11: Built (docs/simp-design.md §12, `crates/elab/src/rewrite/statement.rs`): a statement walk beside the term walk. Positions are the goal, the operands of `∧`, `∨`, `↔`, `¬`, a non-dependent `→`, and a `∀`'s body; each matched on its own; the proof is `goal ↔ next` from `logic`'s new `iff_*_congr` lemmas. Equations and relation steps are carried to the same positions (they did not fire inside a connective before: the lowering puts an operand under a binder). `List::mem_append_iff` joined `List::shape`. Both done-when probes close (`iff_law`, `mem_three` in `lib/_tests/std/tactic/simp_tests.hthr`). Left: `∃` bodies, on simp-under-binders.
