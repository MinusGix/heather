---
title: A call simp computes at a constructor can leave its recursive call unmatched
status: closed
labels: [tactics,simp]
area: tactics
created: 2026-11-11
updated: 2026-11-11
---

`simp_only` computes a call at a constructor first (`docs/tactics/simp-design.md`).
For some functions the result holds the recursive call in a form no law
written over the call matches, and the report spells both sides as "(a term
with no surface spelling)". Found writing `List::foldl_ext`
(`lib/std/data/list_pointwise.hthr`) and `MonoidRel::range_ext`
(`lib/std/algebra/big_operator.hthr`), which work around it with
`then :=`. `foldr` and `map` are not affected.

    theorem u1<A, B>(t: List<A>, a: A, f, g: B → A → B, z: B,
        e: (w: B) → t.foldl(f, w) = t.foldl(g, w), h: f(z, a) = g(z, a)):
        Cons(a, t).foldl(f, z) = Cons(a, t).foldl(g, z)
    { simp_only(h, e) }

refuses after one step (`h`), though `e` at `w := g(z, a)` closes it.
Likely cause, unconfirmed: the unfolded body's recursive call is the
compiled recursion (an accumulator passed through a match whose motive is a
function type, or a section's call), not an application of the named
function, so neither the law's left side nor the display finds it.

Done when the probe above closes, and the refusal spells the two sides.

## Log

- 2026-11-11: Fixed. Two causes, both in computing a call at a constructor (`recursion_at_constructor`, `crates/elab/src/goal_combinators.rs`): (1) `foldl`'s arm is its own recursion (a tail call on the accumulator), and the check that the match selected an arm took the whnf's eliminator head as a stuck match, so the call was never computed and `h` then found `f(z, a)` by unfolding, leaving the raw recursor; an `elim_Wf` firing on a `sup_f` now counts as selected. (2) A recursion on `Nat` (`range`) lowers to `elim_Nat`, which the reduct walk did not refold: `refold::refolded_fire_nat` spells its hypothesis as `λ q̄. g(…, n, q̄, …)` under the same node-for-node check as the `elim_Wf` case. Probes `computed_tail_call`, `computed_nat_recursion`, `computed_left_spelled` in `lib/_tests/std/tactic/simp_tests.hthr`; the `then :=` workarounds in `foldl_ext` and `range_ext` are gone.
