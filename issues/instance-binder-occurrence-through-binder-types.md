---
title: An instance's type parameter reached only through a value binder's type is refused
status: open
labels: [frontend, elaboration, traits, stdlib]
created: 2026-09-18
updated: 2026-09-18
---

The value-generic equality bridge a polymorphic container wants,

```heather
instance<A: DecEq>(xs, ys: List<A>) Decide<xs = ys> { dec := list_eq_dec(xs, ys) }
```

is refused at the declaration:

    the type parameter `A` does not occur in the head `Decide<xs = ys>`, so
    resolution has no way to determine it — a binder is recovered by unifying
    the head against the goal, and one the head does not mention would stay an
    unsolved metavariable at every use site …

`check_binders` (`crates/elab/src/traits.rs`) counts a binder's occurrences in
the head's **class arguments** and **index** only
(`head_var_count`/`index_var_count`). `A` occurs in neither: it reaches this
instance through the *types of the value binders* `xs` and `ys`, which the
check does not walk.

The premise the message rests on does not hold for this shape. `A` is not
undeterminable: candidate-head unification elaborates the instance against the
goal `Decide<Id(List<Nat>, xs, ys)>`, and the lowered `Id` carries the endpoint
type (`docs/decidable-equation-carrier-design.md`), so `?A := Nat` is solved by
the same unification that solves `?xs` and `?ys`. The refusal is the check
being conservative about *where* a binder may be determined from, not the
resolver declining.

## What it costs today

`lib/std/list.hthr` registers `instance(xs, ys: List<Nat>) Decide<xs = ys>`
instead, so `decide` answers an equation between two `List<Nat>` and nothing
else: `List<Char>`, `List<List<Nat>>` and every other element type call
`list_eq_dec` by name. `lib/std/string.hthr` does exactly that, which is fine
there — it wanted the decider, not the goal — but a caller who writes
`decide` at two `List<Char>` gets a missing-instance trace listing eleven
candidates, none of which mentions the reason.

`logic::DecEq<List<A>>`, the carrier-level instance, is **not** affected: its
head is `DecEq<List<A>>`, where `A` occurs.

## Acceptance

`instance<A: DecEq>(xs, ys: List<A>) Decide<xs = ys>` declares, and `decide`
resolves it at `List<Nat>`, `List<Char>` and `List<List<Nat>>`. The
head-absent refusal still fires for a binder nothing determines
(`instance<A> Dec<Bot>`), and the negative controls in
`crates/elab/tests/` that pin the message keep passing.

## What it assumes from elsewhere

- The occurrence rule and its two halves: `docs/value-generic-instances-design.md`
  §4.1, [[instance-binder-occurrence]].
- The endpoint carrier in the key: `docs/decidable-equation-carrier-design.md`.

## Log

- 2026-09-18: Filed from the `Char`/`String` rework, whose generic list
  equality is its first customer.
