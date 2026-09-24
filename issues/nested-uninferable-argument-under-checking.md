---
title: An uninferable call nested in argument position is refused even when the checking position pins it
status: closed
labels: [frontend,elaboration,inference,unification]
created: 2026-09-24
updated: 2026-09-24
---

An uninferable call in *argument* position is refused even when the enclosing
checking position pins its implicit. The spelling with qualified calls fails on
master as well, so this is not a method-syntax problem:

```heather
fn q1(n: Nat, y: BitVec(n)) → BitVec(n) {
    BitVec::band(BitVec::iterate_increment(BitVec::zero(), 3), y)   // refused
}
// likewise R::bump(R::bump(R::mk())) against an expected R(n)
fn a03(n: Nat) → BitVec(n) { BitVec::iterate_increment(BitVec::zero(), 3) }   // ok: one level
```

`band`'s `n` is pinned by `y` and by the expected type. But the first argument
is itself a call whose own implicit is solved only through the argument's
expected type `BitVec(?n)`, and the per-call deferral
(`docs/unifier-completeness-design.md` §3–§5) apparently does not carry a
solution back into a nested deferred call. That blocks method chains whose head
is uninferable (`zero().iterate_increment(3).band(y)`), which the namespace
round (docs/receiver-member-resolution-design.md §7) could only bring to an
honest error. Unifier territory: a candidate for the #1b slice beside
[[vector-literal-length-pins-implicit]] and [[unify-succ-under-addition]], under
[[elab-unifier-completeness]].

## Log

- 2026-09-24: 2026-09-24: Landed as slice #1b (docs/unifier-completeness-design.md §10), with tests in crates/elab/tests/implicit_args.rs. Full suite 2942 passed.
