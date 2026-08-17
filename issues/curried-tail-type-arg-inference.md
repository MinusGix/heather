---
title: "A type parameter that appears only in a curried tail cannot be inferred: zip<A, B>"
status: open
labels: [frontend,elaboration,inference,ergonomics,stdlib]
created: 2026-08-17
updated: 2026-08-17
---

Found writing `std/list`'s `zip` ([[std-list-api]], 2026-08-17). The
declaration is

```heather
fn zip<A, B>(xs: List<A>) -> List<B> -> List<Pair<A, B>> { … }
```

and the call `zip(three(), Cons(4, Nil))` is refused:

```
error: cannot infer the type argument `B` of `zip` here — no argument's type
mentions it; write `zip<…>(…)` to give the type arguments
```

The diagnostic is accurate about its own rule and the workaround works
(`zip<Nat, Nat>(three(), Cons(4, Nil))` checks). What makes it worth an issue
is **which two features collide**, because each is load-bearing and neither is
wrong on its own:

- `zip` is curried because both lists descend together, and the termination
  guard wants one descending argument with the rest fixed
  ([[ih-generalization]]). So `ys: List<B>` is *not* a declared value
  parameter — it is the domain of the returned function type.
- Type arguments are solved against the types of the **declared value
  arguments** ([[exists-type-arg-not-inferred]], closed 2026-08-16). `B`
  appears in no declared argument's type, so there is nothing to solve it
  against.

Over-application ([[call-site-overapplication]]) hides the currying at every
call site *except* this one: the argument is spelled, it just is not visible to
inference. So the language reads as though `zip` took two lists, and then
refuses the inference a two-argument function would have got for free.

## Why the library ranks this above its own inconvenience

Every recursion over two structures is curried — that is not a `zip` quirk,
it is the standing workaround, and `std/nat` alone has `Le`, `leb`, `sub`,
`min`, `max`, `take`, `drop`, `nth`. Those all happen to be monomorphic or to
mention every type parameter in their first argument, so `zip` is the first
place the two rules meet. It will not be the last: `zip_with`, `map2`, and any
`Perm`-style relation between two polymorphic lists have exactly this shape.

## The two routes, and what each costs

1. **Extend argument-directed inference through over-application.** When a
   call supplies more arguments than the declaration's arity, the surplus ones
   are checked against the *result type's* domains — which are already known
   syntactically at the declaration. `B` is then a first-order match against
   `List<B>`, the same match [[exists-type-arg-not-inferred]] taught the
   elaborator to make one level in. Localized, and it fixes the whole class.
2. **Remove the reason for currying** ([[ih-generalization]]): a guard that
   accepts a recursion whose non-decreasing arguments vary. Strictly larger,
   strictly better, and this issue is a datum for it rather than a competitor
   — route 1 stays worth doing even after, because currying is sometimes what
   the writer wants.

## What it assumes from elsewhere

- **[[exists-type-arg-not-inferred]]** (closed) owns the inference rule.
  Assumed here: only that type arguments are solved against the declared value
  arguments' types, first-order.
- **[[ih-generalization]]** owns the currying workaround. Assumed here: only
  that a two-structure recursion has to be curried today.
- **[[call-site-overapplication]]** owns the spelling. Assumed here: only that
  `f(x, y)` elaborates to `f(x)(y)` when `f` is curried.

## Acceptance

`zip(xs, ys)` infers both type arguments at a call where `xs: List<Nat>` and
`ys: List<Bool>` are open variables, and `lib/std/list.hthr`'s comment on
`zip` loses its warning. A negative control stays: a type parameter mentioned
in *neither* the declared arguments nor the curried tail still asks to be
written.
