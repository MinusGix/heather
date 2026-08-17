---
title: A carrier whose type former takes type arguments has no head name: instance C<F<A>(n)>
status: closed
labels: [frontend,elaboration,traits]
created: 2026-08-17
updated: 2026-08-17
---

The carrier widening of [[decide-class]] (`docs/decide-class-design.md` §2)
taught `head_name` to read an applied **type former** — `Le(n, m)`, `Not(P)` —
by walking to the head of an application spine. It reads only the *value*
application spelling. A former written with type arguments refuses:

```heather
fn Rep<A>(n: Nat) -> Type { match n { Zero => A, Succ(k) => Rep<A>(k) } }
instance<A: Inh>(n: Nat) Inh<Rep<A>(n)> { … }
//                           ^ the carrier `Rep<A>(n)` has no head type name
```

while the same former with its type taken as a *value* parameter works:

```heather
fn Plain(A: Type, n: Nat) -> Type { … }
instance Inh<Plain(Top, 0)> { it := tt }        // ok
```

## What it is

`head_name` (`crates/elab/src/traits.rs`) matches
`TyKind::OfExpr(ExprKind::App { head: Var(n), .. })`. With type arguments the
expression is `App { head: TyApp { head: Var(n), args }, .. }`, so the `Var` is
one node further in and the match falls through to `None`. The head name is
`Rep` either way — the type arguments are no more part of the head than the
value arguments are, and the registry has never keyed on a carrier's arguments.

Likely a few lines: peel a `TyApp` head before reading the `Var`, in `head_name`
and in the `expr_size`/`expr_var_count` spine walk beside it (which already has
a `TyApp` case, so only `head_name` may be missing it — check rather than
assume).

## What it assumes from elsewhere

- **[[decide-class]]** owns the widening. Assumed here: only that the head name
  of an applied former is the former's own name, which §2.3 states.
- **[[value-generic-instances]]** owns the value binders. Independent: `Plain`
  above shows the value half works, and this refuses with or without them.

## Where found

Writing the mixed type-and-value test for [[value-generic-instances]]
(2026-08-17). Two defects were stacked there and this is the second — the first
was [[recursive-self-call-type-arguments]], which made `Rep<A>` fail to declare
at all and hid this one behind it.

## Acceptance

`instance<A: Inh>(n: Nat) Inh<Rep<A>(n)>` registers at head `Rep` and resolves
at an open `A` and `n`, and a negative control confirms a former whose result is
not a universe still refuses.

## Log

- 2026-08-17: Fixed, and it was the predicted few lines: `head_name` now walks the application SPINE (a shared `spine_head` through both `App` and `TyApp`) instead of unwrapping one node, so `Tag<A>(n)` — an `App` around a `TyApp` around the `Var` — reaches the same head as `Le(n, m)`. The recursion is entered only from the *applied* case, so a bare name in type position is still not a carrier; that shape is what the original widening admitted and it is unchanged. The issue said to CHECK rather than assume that `expr_size`/`expr_var_count` needed the same, and the check says they did not: both already had a `TyApp` arm, and the positive test proves it rather than the code being read — an instance at `Dec<Tag<P>(n)>` with a `requires Dec<P>` is ADMITTED, which a head measured as size 1 could never be. `names_a_type_former` needed nothing either: it peels `Pi` and `UPi` to a universe, and a type parameter is a leading `Pi` at `Ty l` like any other argument. So the whole defect was one node of unwrapping. Acceptance met and then some: the instance registers at head `Tag`, and it resolves with BOTH arguments open — `fn both_open<B: Dec>(k: Nat)`, where `B` is a constrained type parameter and `k` a binder, so neither can be supplied by reduction. Five tests in crates/elab/tests/traits_type_former_carrier.rs, including the two controls the widening's own §2.3 consequences name: duplicate detection still keys at `Tag` regardless of type arguments, and a former returning `Nat` (`Count<Bot>(n)`) still refuses because reaching a head does not make `Count::Dec` a sentence. docs/decide-class-design.md §2.3 carries the amendment, since that is where a reader looks for what a carrier's head is.
