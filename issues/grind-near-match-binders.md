---
title: "grind: a near match with more than one free binder is skipped"
status: open
labels: [tactics]
area: tactics
milestone: [tac-general]
created: 2026-11-02
updated: 2026-11-02
---

grind matches a lemma's argument up to a definitional step (a near match,
`docs/grind-design.md` §13): the left item is compared with the node by
`Defeq`, its one free binder drawn from the graph's terms. A near match
whose item leaves two or more binders free is skipped, so
`f(Cons(x, ys))` does not meet `f([a] ++ xs)` (both `x` and `ys` free),
and neither does an item with a free type binder (`List::len<?A>(?xs)`).

Options: ask `Defeq` with holes for the free binders and read the
solutions back (the host's unifier solves what the comparison determines,
`Match` does this for a conclusion), falling back to candidates; or draw
the binders as a tuple from the graph, which is a power of its size and
needs a key on the item's head first.

Done when `theorem t<A>(f, g: List<A> → Nat, k: (x: A, ys: List<A>) →
f(Cons(x, ys)) = g(ys), a: A, xs: List<A>): f(List::append([a], xs)) = g(xs)
{ by grind() }` closes.
