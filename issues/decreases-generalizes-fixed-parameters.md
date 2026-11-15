---
title: decreases takes parameters no self-call changes into its recursor
status: open
labels: [frontend,elaboration,proofs,termination]
area: language
milestone: [nh-front]
created: 2026-11-11
updated: 2026-11-11
---

Found by U3c step 2 of [[native-one-compiler]]
(`lib/_tests/native/runtime/rt_span_loops_tests.hthr`). A declaration
`fn f(x̄) → T decreases e { body }` elaborates to a recursor on the bound
that takes **every** parameter (`docs/language/recursion/decreases-unfolding-design.md` §2):

```heather
fn count_from(span: List<BitVec(8)>, length, i, acc: BitVec(64)) → BitVec(64) decreases length.sub(i).toNat() {
    match h: i.unsigned_lt_bit(length) {
        False => acc,
        True => count_from(span, length, i.add(BitVec::ofNat(1)), …),
    }
    …
}
```

`span` and `length` are handed on unchanged by the one self-call, and yet
`count_from::rec` is `(z: Nat) → List<BitVec(8)> → (length i: BitVec(64)) →
BitVec(64) → … → BitVec(64)`, the ih of `count_from::body` takes all four,
and `count_from::ext` asks its two recursions to agree at **every** span and
every length:

    (g1 g2: List<BitVec(8)> → BitVec(64) → BitVec(64) → BitVec(64) → … → BitVec(64)) →
    ((s: List<BitVec(8)>) → (l i a: BitVec(64)) → … → g1(s, l, i, a, p) = g2(s, l, i, a, q)) → …

Structural recursion already generalizes only the parameters a self-call
varies (PR #428, "recursion at the top"). `decreases` does not.

## Why it matters

1. **A loop over a lent span.** A measured `runtime fn` proves its loop from
   `f::ext`: the recursion `again` of `Fun::Guarded` is put in as the second
   ih, and `ext`'s hypothesis is discharged from what `Guarded` assumes of
   `again` (`runtime_measured_instance`, lib/native/runtime/runtime.hthr).
   A function that reads a span is run at one file, the span is not a word,
   and `again` at that file knows nothing of another span, so the
   hypothesis at every `s` is unprovable from the loop's own. The library
   now carries a detour for it: `Fun::GuardedAt` states `Guarded` at every
   world of a family at once, and `Fun::guarded_at` brings it back to one
   world by answering with the function itself wherever the hypothesis
   speaks, behind a decidable test, and by `Tm::tail_sem_ext`
   (lib/native/runtime/rt_loop.hthr). It is sound and proved once, and it
   is there only because the recursor took a parameter the function never
   changes.
2. **Every proof by `f::ext`, `f::irrel` or induction on `f::rec`** carries
   the fixed parameters through each ih application and each hypothesis
   (float/round, creal_lipschitz, relation/transition, algebra/order, hurwitz…), and the
   kernel carries them through every unfolding.

## Fix sketch

In `crates/elab/src/measure.rs`: a parameter that every self-call passes as
itself (the parameter's own variable, at its own position) stays a binder
outside the recursion on the bound. `f::rec(x̄_fixed, z, x̄_varied, h)`,
`f::body`'s ih and the hypotheses of `f::ext` and `f::irrel` then take the
varied parameters only. The measure and the obligations may still read the
fixed ones, which are in scope. A function with no fixed parameter is
unchanged.

What moves with it: the companions' citations in the library that pass a
fixed parameter to an ih (about fifty citations of `::ext`, `::irrel`,
`::rec`, `::body` across sixteen modules; most functions vary everything),
`runtime_measured_instance`, which spells one ih argument per word, and the
designated spellings' documentation (`docs/language/recursion/decreases-unfolding-design.md`
§2, §11). It changes what a module image holds for such a function, so the
round's final run is the exact-image lane.

Done when `count_from::ext`'s hypothesis ranges over `i` and `acc` alone and
`count_guarded` in `rt_span_loops_tests.hthr` is a `Fun::Guarded` at the
span's world with no family; `Fun::GuardedAt` can then go.
