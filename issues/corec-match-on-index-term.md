---
title: Corecursion matching a term its result index mentions is refused
status: open
labels: [codata,coinduction,elaborator]
area: interaction-trees
created: 2026-11-03
updated: 2026-11-03
---

A corecursive definition into indexed codata whose body matches on a term
that the result's index mentions is refused at the arm's constructor, with
a message that does not name the cause:

```
fn sp(E: Events, n: Nat) → CoTree<Nat>(E) { match n { Zero => CRet(0), Succ(m) => CTau(sp(E, m)) } }
fn v(E: Events, n: Nat) → Bisim<Nat>(E, sp(E, n), sp(E, n)) {
    match n { Zero => BRet(0, refl, refl), Succ(m) => BTau(sp(E, m), sp(E, m), refl, refl, v(E, m)) }
}
// error: `BRet` is a constructor of `Bisim`, which is not the expected type here
```

The same happens matching `h: CoTree::obs(E, t)` when the index is
`iter_obs(body, CoTree::obs(E, t))`; the library's own proofs match
`obs(t)` only where the index names `t` (`Bisim::refl`), which is why they
never met it. Reproduced on master at 4a0f52a (before the round-2 friends
work). The workaround is to state the index over a definition that hides
the matched term, as `CoTree::iter_from_unfold` does with
`CoTree::iter_from(E, body, t)`.

Likely cause: the arm's expected type is the carrier/step type with the
index rewritten by the match's motive, and the constructor path
(`build_ctor_m`, `crates/elab/src/codata.rs`) reads its whnf's tag before
the corecursion site recognises the position.

## Done when

Both examples above elaborate, with a test on an indexed codata whose index
mentions the scrutinee (literal and neutral scrutinee).
