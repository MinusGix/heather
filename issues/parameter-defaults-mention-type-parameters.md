---
title: Let a parameter default mention a type parameter (xs: List<A> := Nil<A>)
status: open
labels: [frontend,elaboration,defaults]
area: language
created: 2026-10-12
updated: 2026-10-12
---

A parameter default may mention the value parameters before it
(`k: Nat := n`, [[parameter-defaults-mention-parameters]]), but not a
**type** parameter: `fn f<A>(x: A, xs: List<A> := Nil<A>)` is refused at
the declaration.

## Why it is refused

At the call, each earlier value parameter the default mentions is bound to
the call's argument as an alias (`Cx::aliases`, a kernel term), which is
how a `let` binds a name. A type parameter is a *type* name: the
elaborator resolves it through `Cx::tyvars`, whose entries are binder
positions, not terms, and there is no alias form that binds a type name to
the code a call instantiated it with.

It is rarely needed: the default is checked at the parameter's domain as
the call instantiated it, so `xs: List<A> := Nil` already gets `List<Bool>`
at a `Bool` call without naming `A`. The case that needs it is a default
whose own subterm has no expected type to learn `A` from.

## What would support it

A type-alias entry beside `TyVar`: a name bound to a closed (in the
caller's context) type code, which `elab_ty` reads as `El code`. The
default checker would push one for each mentioned type parameter, from the
call's solved type argument.

## What it assumes from elsewhere

- **[[parameter-defaults-mention-parameters]]** owns how a default reads an
  earlier argument at the call. Assumed here: the spine walkers hand the
  default checker the call's earlier arguments in the committed world. An
  inferred type argument is among them today; one written as `f<…>(…)` is
  already applied in the head, and would have to be read off it.
