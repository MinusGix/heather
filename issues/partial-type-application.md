---
title: No spelling for giving some type arguments and inferring the rest
status: open
labels: [frontend,syntax,ergonomics]
area: language
created: 2026-08-18
updated: 2026-08-18
---

`f<…>` is all-or-nothing: it fills a declaration's leading type parameters
**positionally and completely**, so there is no way to write one and leave the
others to inference.

```heather
fn zip<A, B>(xs: List<A>, ys: List<B>) -> List<Pair<A, B>>
zip<Nat, Bool>(xs, ys)    // both, or
zip(xs, ys)               // neither
```

Raised by the [[named-arguments]] round, which considered and **declined**
fixing it with names (docs/named-arguments-design.md §5.3, §10.1). The reason
is worth keeping: a type argument is a *type*, parsed by `ty()` and lowered by
`elab_ty`, while a named argument's payload is an expression parsed by
`expr()`. The overlap is large but proper — `Nat`, `List<Nat>`, `Type<0>` and
`a = b` read both ways via `expr_as_ty`, while `[Nat; 3]`, `Nat -> Nat` and
`Code(Δ |- T)` have no expression spelling at all — so `zip(A := Nat, …)` would
work for some types and not others, and would reinstate the
"expression read as a type at `Ty l`" coercion that [[at-and-type-arguments]]
deliberately deleted ("it had existed only to paper over this collision").

## The likelier answer

A **hole in the type-argument list**:

```heather
zip<_, Bool>(xs, ys)
```

It stays inside type syntax, needs no second reading of any payload, and
composes with `f<…>` as it stands rather than beside it. `_` in type position
would elaborate to the same meta an omitted type parameter gets — which is to
say, to nothing new: the machinery is `apply_implicit`'s, and what is missing
is only a `TyKind` for the hole and an `elab_ty_app` that mints a meta instead
of a code when it meets one.

Not scheduled. It has no live customer: the case that wanted it
(`psym<Nat>(n, m, p)`) was fixed by making `@` and `<…>` orthogonal.

## What it assumes from elsewhere

- **[[at-and-type-arguments]]** owns the `@`/`<…>` orthogonality. Assumed
  here: only that `<…>` controls type parameters and nothing else does.
