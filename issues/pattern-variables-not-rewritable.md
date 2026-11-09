---
title: A matched list's pattern variables are not locals to subst, and rewrite misses them
status: open
labels: [elaboration, rewrite, proofs]
area: language
created: 2026-11-09
updated: 2026-11-09
---

In an arm `Cons(y, t) => …` of a `match` on a `List`, `t` is not a local:
`subst(h, …)` with `h: t = []` is refused ("neither side of `t = []` is a
local variable the other side does not mention"), and `rewrite(h, …)`
sometimes reports a goal that plainly shows `t` "does not mention the
equation's left side `t`". The pattern variables are aliases of the
scrutinee's projections, so the occurrence a user sees is not the term the
rewrite abstracts.

```heather
import logic; import nat; import list;
fn P(ys, rest: List<Nat>) → Type { match ys { Nil => False, Cons(y, t) => t = rest } }
theorem via_subst(ys: List<Nat>): P(ys, Nil) → ys.len() = 1 {
    match ys {
        Nil => λ h => false_elim(h),
        Cons(y, t) => λ h => subst(h, refl),   // refused: `t` is not a local
    }
}
```

`lib/std/data/perm.hthr` works around it in every head case by a helper
lemma whose parameters are genuine locals (`List::mem_back`,
`picks_len_head`, `occurrences_picks_head`, the `*_head` lemmas), passing the
pattern variables in.

## Done when

A pattern variable is a local for `subst` (eliminated by reverting what
mentions it, as for a λ-bound one) and an occurrence for `rewrite`, and the
helpers in `std/perm` can be inlined.
