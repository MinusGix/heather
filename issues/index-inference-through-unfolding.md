---
title: Pin a generic theorem's indices from a hypothesis whose type unfolds to its statement
status: closed
labels: [traits,elaboration,inference]
area: language
created: 2026-11-02
updated: 2026-11-02
---

Found by the math-classes round (docs/library/lattice-structure-design.md §4). `Rat::same_trans` wanted to call

    OrderedSemiring::cross_same_trans(x.num, x.den.int(), y.num, y.den.int(), z.num, z.den.int(), q, hxy, hyz)

with `hxy: x ≈ y` at `Rat`, which is `Rat::Same(x, y)` and unfolds to exactly the theorem's `a * d ≈ c * b` at `Int` (`x.num * y.den.int() = y.num * x.den.int()`). The call is refused: `no instance for OrderedSemiring<A>(#op≈, #op<, #op<=, #op+, #op*)`, every candidate "built, but not of the goal type". Restating the two hypotheses at `Int` first (`let h1: (x.num * y.den.int() ≈ y.num * x.den.int()) = hxy;`) and passing `h1` checks. Writing the call's type with `≈` at `Int` does not help, nor does `<Int>`.

So an argument's type pins indices only when it is spelled in the indices' own symbols. A hypothesis whose type is a carrier's definition (`Rat::Same`, `Dyadic::Le`) does not, even when one δ step gives the statement. The same holds for the expected type, which is [[relational-index-inference-from-goals]]'s territory; this issue is the argument side.

Wanted: when an argument's declared type is a δ-redex whose head is a global definition and its unfolding matches the parameter's type, unify against the unfolding before giving up on the indices, bounded to a step or two so that resolution never runs whnf at large. The refusal should at least name the argument that failed to pin anything, since the current message lists candidates that were "not of the goal type" without saying which argument disagreed.

Controls: the restated call (works today), a hypothesis at `Dyadic::Le` against an `OrderedSemiring` theorem, and a negative control whose unfolding genuinely does not match.

## Diagnosis

The call never got as far as needing an unfolding. `unify_tm`'s rigid-spine
alignment (a flexible operation spine learns a rigid head of the same value
arity, the rule [[relational-index-inference-from-goals]] added) read
`?≈(?*(a, d), ?*(c, b))` against `Rat::Same(x, y)` and recorded
`?≈ := Rat::Same`, though `?≈ : Int → Int → Type` was already fixed by the
explicit `Int` arguments. The expected type `x ≈ z` did the same. Nothing
checked the solution against its slot, so instance search ran at
`OrderedSemiring<Int>(Rat::Same, …)` and every candidate was "built, but not
of the goal type". Restating at `Int` worked because the hypothesis then
spelled `RelId<Int>` and pinned the slot correctly.

## Implementation

- The unifier's one write holds each solution to its slot's declared type
  (`SolutionCheck`, crates/elab/src/solution_check.rs, since
  [[unifier-checked-assignment]]; this issue first added it as a post-hoc
  `reject_ill_typed_solutions` over Π slots after a whole read). A solution
  whose type cannot be inferred is kept, so the read stays learn-only and
  the kernel still judges the call.
- When a write was refused, `unify_arg_ty` reads the argument type's first
  `INDEX_UNFOLD_STEPS` (8) reducts, nearest first. It reads only those that
  are still applications of a declaration, stops at the first that teaches
  something that fits, and falls back to the existing whnf retry. Calls whose
  read is clean never step.
- With `?≈` left open, the designation rung fills `≈ := RelId<Int>` from the
  carrier as it does for the restated call. `Rat::same_trans` now passes
  `hxy`, `hyz` as stated.
- On the diagnostic: the misleading "not of the goal type" list no longer
  arises from this shape. A hypothesis whose unfolding does not match (the
  negative control) is refused at that argument with its type and the
  expected one. An index that neither a designation, the goal nor an
  unfolding pins keeps the existing "the index `R` … is not pinned" message,
  which names the index, not the argument.

Probes: `lib/_tests/std/num/rat_tests.hthr` (`cross_trans_as_stated`, the
restated control, the swapped negative control) and
`lib/_tests/std/num/float/dyadic_tests.hthr` (`Dyadic::Le` against
`OrderedAddMonoid::add_le_mono_r` at `Rat`, and `trans_through_rat`, where an
implicit `R` with no designation and no expected type is pinned only by the
hypothesis's unfolding `Rat::Le(a.rat(), b.rat())`). Without the slot check
all three positive probes are refused. Without the reduct walk only
`trans_through_rat` is refused.

## Log

- 2026-11-02: Fixed by holding inferred operation indices to their slots' types and reading the argument's δ-reducts after a rejection (see Implementation). scripts/test --pr: 2985 passed, 0 failed, 2 ignored.
