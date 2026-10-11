---
title: Let a function own member declarations (theorem f::name)
status: closed
labels: [frontend,syntax,elaboration,modules]
created: 2026-10-10
updated: 2026-10-11
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
- 2026-10-11: LANDED. A `fn` owns a member namespace: check_decl's owner rule widens from carriers to any global that keeps its body (Elaborator::names_a_function, a bodied Ψ `Tm`), so `theorem ten_pow::pos(…)` declares the qualified string exactly as a type's member does and the §4 regime resolves it unchanged — in-module, imported, by module path (`d::double::zero`) and through a facade's `export d::{double::zero}`. Two modules attaching one member to one function are the ordinary ambiguity. Refusals: a theorem or axiom owner ("`t` is a theorem, so `t::x` attaches to nothing"); an unknown owner (message now names functions too); a function named like a module its file sees, since `f::pos` reads as module `f`'s `pos` first. Across modules, where the declarer cannot see the clash, names::resolve_kinds now answers Ambiguous when a module path and a member are spelled alike (member's module first, so the advice `m::f::pos` reaches it) — the growth invariant: a module growing a `pos` can no longer silently reinterpret a member reference. `f.pos(…)` is unreachable by design (the receiver's type is a function type, no namespace); when no ambient `pos` exists the dot call is refused naming `f::pos(…)` instead of "unbound". Tests: crates/elab/tests/type_members.rs, the function-owned section (11 tests). Not changed, by the same decision as type members: an import list cannot name a qualified member (issues/type-owned-members-receiver-slice.md); and no library declaration moved (`ten_pow_pos` stays until [[pos-binder-sugar]] gives it the `f::pos` name).
