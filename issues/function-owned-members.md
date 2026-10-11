---
title: Let a function own member declarations (theorem f::name)
status: open
labels: [frontend,syntax,elaboration,modules]
created: 2026-10-10
updated: 2026-10-10
---

Let a `fn` own members, so a theorem about one function can be declared and
named under it: `theorem ten_pow::pos(i: Nat): 0 < ten_pow(i)`. Today a
member attaches only to a type, and that declaration is refused ("`ten_pow`
is not a type or a type former in scope").

Many theorems are about one function rather than about its result type, and
the shared namespace gets `ten_pow_pos`-style names. [[pos-binder-sugar]]'s
result form needs a deterministic name for the fact it produces, and
`f::pos` is that name.

`::` is the spelling. `ten_pow.pos` would collide with receiver dispatch,
which resolves `f.m` by the type of `f` (a function type here).

## Acceptance

- `theorem f::name(…)` declares and `f::name(…)` resolves, in-module and
  imported.
- A function member and a same-named type member stay distinct.
- Diagnostics display the qualified name.

## Log

- 2026-10-10: Filed from [[positivity-evidence]] (design note §6 B).
