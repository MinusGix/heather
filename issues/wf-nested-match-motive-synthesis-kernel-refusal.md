---
title: Nested motive-less matches on tier-1 arm aliases: the elaborator accepts a term the kernel refuses
status: open
labels: [frontend,elaboration,kernel,robustness]
created: 2026-09-18
updated: 2026-09-18
---

Found closing [[utf8-encode-decode-strictness]] (2026-09-18). The first
spelling of `utf8::strict_below` was

```heather
theorem strict_below(n: Nat): Bounded(n) {          // (bytes) → list_len(bytes) <= n → Strict(bytes)
    match n {
        Zero => …,
        Succ(k, ih) => λ bytes => match bytes {
            Nil => …,
            Cons(b, rest) => match rest {
                Nil => λ hl => bounded_leaf0(k, ih, b, hl),
                Cons(c1, rest2) => match rest2 {
                    Nil => λ hl => bounded_leaf1(k, ih, b, c1, hl),
                    Cons(c2, rest3) => match rest3 {
                        Nil => λ hl => bounded_leaf2(k, ih, b, c1, c2, hl),
                        Cons(c3, rest4) => λ hl => bounded_leaf3(k, ih, b, c1, c2, c3, rest4, hl),
                    },
                },
            },
        },
    }
}
```

— three nested motive-less `match`es on a λ-bound `List<BitVec(8)>`, none of
them on the recursion's own parameter (that is `n`), each leaf a call to a
lemma stated at the constructor spelling (`bounded_leaf1` returns
`Strict(Cons(b, Cons(c1, Nil)))`). **The elaborator accepted it and the
kernel refused it**: `the kernel rejected strict_below: NotConvertible`,
naming no arm. Every leaf lemma checked on its own. Writing the motives out,
one per level —

```heather
Cons(b, rest) => match rest as λ r => list_len(Cons(b, r)) <= Succ(k) → Strict(Cons(b, r)) {
    Nil => λ hl => bounded_leaf0(k, ih, b, hl),
    Cons(c1, rest2) => match rest2 as λ r2 => list_len(Cons(b, Cons(c1, r2))) <= Succ(k) → … {
```

— made the same proof check, so the terms differ only in the motive a nested
`match` on a tier-1 arm's alias is given. A synthesized motive abstracts the
alias (a projection `nth(cs; ι₀)`, tier 0 §5.1) out of a goal spelled at
`sup(ℓ; cs)`, where it is not a subterm; `docs/list-course-of-values-design.md`
§7.3 records the same limit on the window path ("synthesis has to recover it
from a reduced goal, and at depth three it does not") and §7.4 the cure there
(spell the arm's goal at the constructor rebuilt around the child). This is
the plain path, one level shallower, with the same symptom.

Two things to settle, the first being the one that matters:

1. **Why the elaborator's own check passed.** Whatever it accepted, the
   kernel gate refused a whole theorem with no location — the worst outcome
   the two-checker design allows, and the thing `docs/testing-generated-terms.md`
   exists to prevent. Either the elaborator's conversion has an η the kernel's
   lacks (a children-vector η at the sup, §7.4's `(nth cs' ι₀, ⟨⟩) ≡ cs'`), or
   its check of the arm was against a goal it had already refined and the
   emitted motive was another.
2. **Synthesize at the rebuilt constructor for every nested `Wf` match**, as
   §7.4 does for the window, or refuse at the nested `match` with a message
   that names the `as` spelling that works.

Repro: `lib/std/utf8.hthr` at the commit that closed the strictness issue,
with `strict_below`'s four `as` motives deleted.

## What it assumes from elsewhere
- **[[list-course-of-values-recursion]]** owns the rebuilt-constructor
  spelling (§7.4). Assumed here: only that it is applied on the window path
  and not on the plain one.
