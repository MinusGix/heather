---
title: Let a parameter default mention an earlier parameter (k: Nat := n)
status: open
labels: [frontend,elaboration,defaults]
created: 2026-10-12
updated: 2026-10-12
---

A parameter default may not mention another parameter today:
`fn f(n: Nat, k: Nat := n)` is refused at the declaration ("a default
cannot mention a parameter yet"). Defaults that mention only globals, and
tactic defaults whose *goal* mentions earlier parameters
(`h: 0 < n := omega`), work (docs/named-arguments-design.md §9.6).

## Why it is refused rather than half-supported

A default runs at the call, checked at the parameter's domain with the
call's earlier arguments already substituted, in the caller's locals made
unreachable by name (`Cx::hygienic`). In that context a parameter is not a
name at all: the default sees `0 < 5`, not `0 < n`. Resolving `n` to
anything the caller can spell would be the dynamic scoping §9.4 rejects.

## What would support it

Bind each earlier parameter's name, in the default's scope, to the call's
elaborated argument for it, as a `let` alias does (`Cx::aliases` holds a
kernel term). The marker check (`Elaborator::elab_param_default`) has only
the instantiated domain; the arguments live in `apply_implicit`'s scratch
world (explicit arguments elaborated in declaration order, implicits as
solved metas). So the marker would need the zonked prefix of the
application handed to it, the way a `ResolveOb` carries `applied`.

A default that mentions a *later* parameter stays refused: the telescope
is ordered (§9.4).

## What it assumes from elsewhere

- **[[named-arguments]]** owns how a default is filled at a call. Assumed
  here: an omitted default reaches the spine walkers as a named argument
  whose payload is the `PARAM_DEFAULT` marker.
