---
title: rewrite by an induction hypothesis inside an unfolded recursive goal
status: open
labels: [frontend,tactics,recursion]
area: tactics
created: 2026-10-24
updated: 2026-10-24
---

A proof by structural induction that rewrites with its own hypothesis fails
when the goal is the unfolding of a structural `fn`:

```
inductive T { L, N(a: T, b: T) }
fn idr(t: T) -> T { match t { L => L, N(a, b) => N(idr(a), idr(b)) } }
theorem ok(t: T): idr(t) = t {
  match t { L => refl, N(a, b) => rewrite(ok(a), ok(b), refl) }
}
```

reports that the goal `idr(N(a, b)) = N(a, b)` does not mention `idr(a)`.
The goal as written does not, and its exposed form (`matching::expose`, one
`whnf` of each side) holds the recursor applied to `a`, not `idr(a)`, so
neither spelling has a subterm with the left side's head. The note on the
error, "as written or one unfolding of it", promises more than the search
does. Found while testing mutual recursion over a mutual family
(`docs/mutual-inductive-design.md` §7), where the same happens one δ-step
further away; the tests there use a congruence lemma checked by conversion
instead.

What a fix needs: the exposed goal spelled with the declaration's own name
at its recursive positions, where the recursor applied to a subterm is the
declaration applied to it (the structural guard knows which recursor a
declaration compiles to). Keying the search on the left side's unfolding is
not enough on its own: both the unfolded left side and the exposed goal hold
the raw recursor, and the search keys on a global head.

## Log

- 2026-10-24: Filed from the mutual inductive families round.
