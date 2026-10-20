---
title: Pin a generic call's class indices before unifying its result with an unfolded expected type
status: closed
labels: [elaborator,classes,inference]
created: 2026-10-19
updated: 2026-10-20
---

A generic theorem whose result is a constrained predicate, such as `OrderedAddGroup::abs_lt_add<A: OrderedAddGroup(≈, <, <=, +)>(…): AbsLt(x + y, e + d)`, is refused for want of an instance when the expected type is the predicate's unfolding (`-(e + d) < x + y ∧ x + y < e + d` at `Rat`), even though the carrier is pinned by an explicit point. The same call with a `let` naming `AbsLt(…)` checks. Inside generic proofs the same happens when a hypothesis of type `Close(x, y, e)` is passed where `AbsLt(x - y, e)` is expected; lib/std/ordered_field.hthr works around both with `let`s, and docs/showcase/ordered_field_client.hthr shows the client workaround.

Related: generic theorems must take their points explicitly, because with implicit endpoints a hypothesis `?lt(?x, ?y)` is not solvable against `Rat::Lt(a, b)` before the carrier is known, and an explicit type argument (`le_of_lt<Rat>(h)`) does not pin the indices either.

Expected: once the carrier is known from an explicit point, the class indices are filled from the carrier's designations before the result is unified with the expected type, so a δ-unfolding comparison can succeed.

## Log

- 2026-10-20: Fixed. The cause was not ordering but the unifier: its application congruence aligned two spines from the right whatever their heads, so `AbsLt(?A, ?≈, ?<, ?≤, ?+, ?d, x, e)` against `-e < x ∧ x < e` learned `?+ := Rat::Lt`, and against `Close(x, y, e)` learned every index one place over; instance search then met a goal with wrong indices. `unify_tm` now learns nothing from two rigid applications of different spine lengths (crates/elab/src/unification.rs), so the indices stay open for the scope or designation rung and conversion does the unfolding. An explicit type argument (`le_of_lt<Rat>(x, y, h)`) now pins the indices too: the designation rung reads a carrier that has no slot off the call's spine. The eight bridging `let`s in lib/std/ordered_field.hthr and docs/showcase/ordered_field_client.hthr are gone; tests in crates/elab/tests/lib_std_ordered_field.rs (`an_unfolded_predicate_meets_its_name`, with a swapped-conjuncts control) and a unit test beside the rule. Implicit endpoints stay out of scope by design: generic theorems take explicit points (docs/constructive-ordered-field-design.md, "Calling a generic theorem"), so nothing is owed there.
