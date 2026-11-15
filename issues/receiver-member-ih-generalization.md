---
title: IH generalization does not see a self-call spelled as a receiver, so a varying parameter cannot be a method
status: closed
labels: [frontend,elaboration,recursion,ergonomics]
created: 2026-09-18
updated: 2026-09-24
---

A structurally recursive function that varies a non-decreasing parameter checks
as a freestanding `fn` and is **refused** when the identical body is a
type-owned member, because the IH-generalization analysis
(`docs/tactics/ih-generalization-design.md`) does not recognize a self-call spelled as
a receiver.

Repro (`probes/str/p13.hthr@ef3961a`, 12 lines, `import logic; nat; list;`):

```heather
inductive Tree { Leaf(n: Nat), Node(l: Tree, r: Tree) }

// checks
fn flat(t: Tree, tail: List<Nat>) → List<Nat> {
    match t { Leaf(n) => Cons(n, tail), Node(l, r) => flat(l, flat(r, tail)) }
}

// refused, same body
fn Tree::flat_m(self t: Tree, tail: List<Nat>) → List<Nat> {
    match t { Leaf(n) => Cons(n, tail), Node(l, r) => l.flat_m(r.flat_m(tail)) }
}
// error: recursive call to `flat_m` must pass `tail` unchanged: … A parameter is
// generalized into the motive … only when the `match` is checked against a known
// result type and the varying call is visible in its arms …; here it was not
```

The "varying call is visible in its arms" test evidently looks for the self-call
as a direct application and misses `x.f(…)`. Nothing about the recursion
differs: same scrutinee, same decreasing argument, same varying parameter.

There is no spelling that works around it. A qualified self-call inside the
member is refused too — `Tree::flat_d(l, …)` gives "`Tree::flat_d` is qualified
by `Tree`, which is neither an imported module nor a type in scope here" — so a
type-owned member is reachable *only* through a receiver, and the analysis does
not see receivers. That second half is [[type-owned-namespaces]]'s missing
non-receiver reach, logged there.

Found converting `docs/showcase/calc_text.hthr`'s derivation theory to
`Derivation::` members ([[sequence-parser-source]], 2026-09-18). `tier`,
`meaning`, `spelling`, `WellFormed` and `cong_spell` all converted cleanly;
`spell` is a difference-list spelling whose whole point is varying its `tail`,
so it is the one declaration that has to stay freestanding, in a file where
every neighbour is a member. That asymmetry is the cost: a difference list — the
idiom that removed every `append_assoc` from that showcase — cannot be a method.

## Log

- 2026-09-24: 2026-09-24: No longer reproduces on master: the issue's `Tree::flat_m` repro and the qualified self-call both check. It closes when calc_text's `spell` converts to a member in the namespace round (docs/language/classes/receiver-member-resolution-design.md §5).
- 2026-09-24: 2026-09-24: Landed with the namespace round (docs/language/classes/receiver-member-resolution-design.md; §7 lists what was built and where it deviated). Full suite 2939 passed.
