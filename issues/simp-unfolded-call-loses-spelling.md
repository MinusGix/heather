---
title: A call simp computes at a constructor can leave its recursive call unmatched
status: open
labels: [tactics,simp]
area: tactics
created: 2026-11-11
updated: 2026-11-11
---

`simp_only` computes a call at a constructor first (`docs/simp-design.md`).
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
