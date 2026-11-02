---
title: Pin a generic theorem's indices from a hypothesis whose type unfolds to its statement
status: open
labels: [traits,elaboration,inference]
area: language
created: 2026-11-02
updated: 2026-11-02
---

Found by the math-classes round (docs/lattice-structure-design.md §4). `Rat::same_trans` wanted to call

    OrderedSemiring::cross_same_trans(x.num, x.den.int(), y.num, y.den.int(), z.num, z.den.int(), q, hxy, hyz)

with `hxy: x ≈ y` at `Rat`, which is `Rat::Same(x, y)` and unfolds to exactly the theorem's `a * d ≈ c * b` at `Int` (`x.num * y.den.int() = y.num * x.den.int()`). The call is refused: `no instance for OrderedSemiring<A>(#op≈, #op<, #op<=, #op+, #op*)`, every candidate "built, but not of the goal type". Restating the two hypotheses at `Int` first (`let h1: (x.num * y.den.int() ≈ y.num * x.den.int()) = hxy;`) and passing `h1` checks. Writing the call's type with `≈` at `Int` does not help, nor does `<Int>`.

So an argument's type pins indices only when it is spelled in the indices' own symbols. A hypothesis whose type is a carrier's definition (`Rat::Same`, `Dyadic::Le`) does not, even when one δ step gives the statement. The same holds for the expected type, which is [[relational-index-inference-from-goals]]'s territory; this issue is the argument side.

Wanted: when an argument's declared type is a δ-redex whose head is a global definition and its unfolding matches the parameter's type, unify against the unfolding before giving up on the indices, bounded to a step or two so that resolution never runs whnf at large. The refusal should at least name the argument that failed to pin anything, since the current message lists candidates that were "not of the goal type" without saying which argument disagreed.

Controls: the restated call (works today), a hypothesis at `Dyadic::Le` against an `OrderedSemiring` theorem, and a negative control whose unfolding genuinely does not match.
