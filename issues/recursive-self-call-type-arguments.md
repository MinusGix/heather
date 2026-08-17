---
title: A recursive self-call cannot be written with explicit type arguments
status: open
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
