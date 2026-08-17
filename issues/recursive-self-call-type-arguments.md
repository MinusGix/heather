---
title: A recursive self-call cannot be written with explicit type arguments
status: closed
labels: [frontend,elaboration,diagnostics]
created: 2026-08-17
updated: 2026-08-17
---

A `fn`/`theorem` that is generic in a type cannot name its own type arguments in
its **recursive** call, and the diagnostic denies the declaration a reader is
looking at:

```heather
fn twice<A>(a: A, n: Nat) -> A { match n { Zero => a, Succ(k) => twice<A>(a, k) } }
//                                                              ^ `twice` takes no
//                                                                type arguments
```

`twice` visibly takes one. The same call written *outside* the declaration is
fine, and so is the implicit spelling inside it:

| spelling | verdict |
|---|---|
| `twice<A>(a, k)` inside `twice`s own body | **refused** |
| `twice(a, k)` inside its own body | ok — `A` infers |
| `twice<Nat>(a, k)` from another declaration | ok |

So the self-reference is in scope with its parameter list but *without* its type
parameters, and only the `TyApp` route notices.

## Why it is worth a line

Not because the workaround is hard — it is "drop the `<A>`" — but because the
message actively misinforms. It states a property of the declaration ("takes no
type arguments") that is false, and it is printed at the one place a reader
cannot check it against a different declaration, since the caller and the callee
are the same text. A reader who trusts it concludes the language has no
recursive polymorphic functions.

## Where found

Writing a mixed type-and-value carrier for
[[value-generic-instances]] (2026-08-17):
`fn Rep<A>(n: Nat) -> Type { match n { Zero => A, Succ(k) => Rep<A>(k) } }`
refused, and the cascade made the next three declarations look broken too — the
head never registered, so every later `Rep<A>(…)` reported the same thing. The
test that wanted it was rewritten around a non-recursive former instead, which
is why nothing in the suite covers this.

## Acceptance

`twice<A>(a, k)` inside `twice` elaborates, or — if there is a reason the
self-reference must not carry its type parameters — the diagnostic says *that*,
naming the recursive call rather than the declaration.

## Log

- 2026-08-17: Fixed. A self-call may now write its own type arguments — `f<A>(…)` inside `f`'s body — and they are checked to BE the declaration's own parameters, in order, then dropped: it is the same call as `f(…)`, and `twice<Nat>(7, 3) = 7` is still refl, so the lowering is still the recursor. The rule, which the fix states rather than assumes: a self-call is always at the declaration's own instantiation, because the recursion becomes an `elim` whose motive is fixed outside it and whose type parameters are λ-bound outside that — there is no position in the emitted term for a second instantiation. Recursing at a different one is polymorphic recursion, needs a fixpoint, and is exactly what [[match-recursion]]'s discipline exists to avoid; it now says so, naming the offending argument, instead of leaving a reader to infer it from a scope puzzle. Why accept rather than refuse uniformly: the self-name is not a global while its own body elaborates, so `elab_ty_app`'s `params_of` found nothing and the arity complaint denied a declaration the reader was looking at — at the one place the claim cannot be checked against a different declaration, since caller and callee are the same text. Four refusals replace the one wrong message: a different instantiation (polymorphic recursion), the wrong count, type arguments on a monomorphic self-call, and a bare `f<A>` with no call (the self-name is not a value — the message a bare `f` already gave). The guard is untouched and still refuses an unguarded self-call written with type arguments; `@` and `<…>` still compose. docs/surface-polymorphism.md §7.1 is the rule; ten tests in crates/elab/tests/polymorphism.rs. Restoring the test this cost [[value-generic-instances]] uncovered a SECOND defect underneath it, now [[type-former-carrier-with-type-arguments]]: `head_name` reads an applied type former's spine only in its value-application spelling, so a carrier `Rep<A>(n)` still has no head name. Independent of this one, which was hiding it.
