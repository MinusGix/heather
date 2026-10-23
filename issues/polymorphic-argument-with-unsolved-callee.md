---
title: A polymorphic function passed as an argument cannot be instantiated while the callee's own type argument is unsolved
status: closed
labels: [frontend,elaboration,inference]
created: 2026-08-17
updated: 2026-09-28
---

Found by wave L2′ ([[std-list-l2-prime-laws]]) writing `zip_swap`. Ranked
**last** of the round's four: the workaround is an η-expansion and costs one
line. It is filed because of its *shape*, not its cost — it is the third round
running in which the thing the language could not write is a polymorphic callee
whose type argument is still unsolved ([[curried-tail-type-arg-inference]] and
[[match-arg-of-polymorphic-callee-needs-motive]], both closed 2026-08-17, were
the first two).

```heather
map(zip(xs, ys), swap) = zip(ys, xs)
// error: this argument of `map` was deferred — the type of its parameter `f`
// still mentions an implicit that could not be inferred
```

The two halves each work alone, which is what makes this the same collision the
other two were:

- **With the callee's type argument spelled, the bare polymorphic argument is
  fine.** `map<Pair<A, B>, Pair<B, A>>(zip(xs, ys), swap)` checks — so an
  argument's own implicits *are* solved from a known expected type.
- **With the argument η-expanded, the callee's type argument is fine.**
  `map(zip(xs, ys), λ (q: Pair<A, B>) => swap(q))` checks, and this is what
  `lib/std/data/list.hthr` ships, because it is shorter than the type arguments.

What cannot happen is both at once: solving `map`'s `B` requires knowing
`swap`'s instance, and `swap`'s instance would come from `map`'s parameter type,
whose codomain is that same unsolved `B`. First-order unification of
`Pair<?X, ?Y> -> Pair<?Y, ?X>` against `Pair<A, B> -> ?B2` decides all three in
one pass — domain-only, which is the rule
[[exists-type-arg-not-inferred]] already established — so the fix is plausibly
to unify the argument's *type* against the parameter rather than to elaborate
the argument against it and defer.

## What it assumes from elsewhere

- **[[exists-type-arg-not-inferred]]** owns the "type arguments come from the
  value arguments' own types, first-order and domain-only" rule. Assumed here:
  only that it exists and that an unapplied polymorphic name has no value
  argument to feed it.

## Related

- **[[deferred-argument-diagnostic-show-rough-type]]** owns displaying the
  selected callee and useful rough type information when this deferred path is
  reached by an ill-typed application.

## Acceptance

`map(zip(xs, ys), swap)` checks with no type arguments and no η-expansion, and
`lib/std/data/list.hthr`'s `zip_swap` is restated on it. Negative control: an
argument whose implicits are genuinely undetermined by the parameter type still
reports, and still names which implicit.

## Log

- 2026-08-26: `std/relation` supplied a second customer: the statement of
  composition associativity could not infer the intermediate carriers in
  `Compose(Compose(R, S), T)`.  Explicit `Compose<A, B, C>` arguments make it
  check.  This is the same dependency shape—a polymorphic function-valued
  argument and an outer call whose own carriers are not yet fixed—so it stays
  here rather than becoming a relation-specific inference issue.
- 2026-09-28: Fixed through partial-domain instantiation in the deferred-argument retry. A bare global or local/alias polymorphic function gets a separate scratch world; only committed, binder-independent parts of the outer parameter type may solve its implicits. Once its instance is complete, ordinary checking emits it and its type solves the outer call's remaining implicits. Unresolved and withheld outer slots cannot escape into inner solutions.

  `List::zip_swap` now states `xs.zip(ys).map(Pair::swap)`. Regression coverage includes open and concrete pairs, inference without an expected result type, reversed argument order, local/alias skeletons, value implicits, named undetermined implicits, and binder-capture refusal. The former negative `compose(id, id, n)` test now checks, including an open-input inference case; nested relation composition also checks without explicit carriers. Updated the unifier design and [[elab-unifier-completeness]]'s former boundary.

  Validation: full `scripts/test` — 3032 passed, 0 failed, 5 ignored.
