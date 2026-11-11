---
title: A view of Exists(P) does not present its predicate
status: closed
labels: [tactics,host]
area: tactics
created: 2026-11-11
updated: 2026-11-11
---

The host's `View` of a type that is a value-parameterised record
(`Exists<A>(λ x => …)`) answers `Other`. `view_instance`
(`crates/elab/src/host.rs`) unifies the type with the declaration's
template at unknown arguments, and the unifier leaves the predicate
unsolved: the lowering holds it applied and uncontracted,
`El(app(λ…; witness))`, against the template's `app@(?P; witness)`, and
`sols` comes back `[A, None]`.

So a Heather tactic cannot look inside an existential. The cost seen so
far: `by simp()` collects default sets from the types of the goal's
subterms (`simp_types`, `lib/std/tactic/simp.hthr`), and a `List` that
occurs only inside an `∃` brings no `List::shape`
(`docs/simp-design.md` §13). `simp_only` reads the predicate off the
lowering directly (`Statements::existential`,
`crates/elab/src/rewrite/statement.rs`), which is the read a view could
share.

Wanted: `View` of `Exists(P)` is `HGlobal(Exists, [A, P])`, as for a class
dictionary's type, and `P` views as a λ that `Open` enters.

Done when

    theorem t<A>(xs, ys: List<A>):
        Exists(λ (a: A) => Mem(a, xs ++ (ys ++ Nil))) ↔ Exists(λ (a: A) => Mem(a, xs) ∨ Mem(a, ys)) { by simp() }

closes.

## Log

- 2026-11-11: Fixed: `view_instance` (`crates/elab/src/host.rs`) reads a value argument the unifier leaves unsolved where the template applies it (`applied_values`: the template's `El(?j(a))` against the type's `El(F(a))` at the same position of the lowering, `F` strengthened past the binders crossed), and keeps the conversion check of the template at what was read. The done-when theorem is the probe `defaults_below_exists` in `lib/_tests/std/tactic/simp_tests.hthr`.
