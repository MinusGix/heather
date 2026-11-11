---
title: A record at one value parameter is accepted where another is expected, and the kernel refuses
status: open
labels: [elaborator,diagnostics]
area: language
created: 2026-11-11
updated: 2026-11-11
---

A value of `Exists(P)` checks, in the elaborator, at `Exists(Q)` for a
different predicate `Q`, and the declaration is then refused by the kernel
gate with its own message:

    theorem plain<A>(xs, ys: List<A>, w: Exists(λ (a: A) => Mem(a, xs) ∨ Mem(a, ys))):
        Exists(λ (a: A) => Mem(a, xs ++ ys)) { w }
    // the kernel rejected `plain`: NotConvertible. the type of this expression
    // does not convert to `Exists<…>(λ (x: A) => Mem(x, xs ++ ys))` (its own
    // type has no surface spelling)

Nothing unsound: the gate refuses. But the refusal is the kernel's, at the
whole declaration, where every other mismatch is the elaborator's "this has
type … but … is expected here" at the expression, with both types spelled.
Found while probing `simp_only(…, then := w)` at an existential
(`issues/simp-under-binders.md`), where it read as a fault of the simplifier.

Wanted: the elaborator's own check compares the value arguments of a
value-parameterised former, and the message spells both.

Done when the declaration above is refused as a type mismatch at `w`.
