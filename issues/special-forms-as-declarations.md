---
title: j/refl/cong/absurd/inj as ordinary declarations, not elaborator special forms
status: open
labels: [frontend,elaboration,design]
created: 2026-07-27
updated: 2026-07-27
---

Split out of [[surface-universe]] on 2026-07-27 so that issue could close:
its §6 named this as what the Type Session unblocks, and phase 3 unblocked it,
but it is a round of its own and was going to sit in a closed issue's log
otherwise.

`j`, `refl`, `cong`, `absurd` and `inj` are elaborator special forms — the
elaborator recognizes the name and builds the kernel term. Each is expressible
as an ordinary declaration now that a motive is an ordinary λ
([[motives-as-lambdas]]) and a type is an expression at a universe. Making
them declarations is [[frontend-roadmap]]'s round-two principle applied to the
last places the elaborator still knows a name by heart: fewer special features
in the elaborator, more fundamental features in the language.

## What this issue owns

Whether these five stop being special forms, and what it costs. Nothing else.

## What it assumes from elsewhere

- **[[surface-universe]]** (closed) owns the universe. Assumed: a motive is
  writable as an ordinary λ, and `Type<n>` is writable in a binder. Its §6
  states the catch below and is the place to re-read if the level story moves.
- **[[surface-polymorphism]]** (closed) owns type parameters. Assumed: a
  declaration can be generic in a type at a *concrete* level.

## The catch, from `docs/surface-universe.md` §6, stated not discovered

In full generality a motive is polymorphic in its **level**, which is `UPi`,
which is layer m. So these become declarations **at concrete level 0** — where
every current use lives — and full generality waits for the modal round. A
round that promises more than level 0 is mis-scoped.

## Open, and not yet examined

- `inj`'s spelling already moved once (`inj(p, k)`, [[method-receiver-position]]);
  whether a declaration can carry the same shape is unchecked.
- `absurd`/`inj` are generated *per declaration* by the inductive lowerings
  ([[inductive-compiler]]), so "an ordinary declaration" may mean a generated
  one, which is [[generators-in-the-language]] territory rather than a
  hand-written prelude entry. **This is the first thing to settle** — it
  decides whether this is a small round or a dependency on the meta layer.

## Log

- 2026-07-27: Filed, splitting the residue out of [[surface-universe]] so that
  issue could close rather than stay open for a follow-on it did not own.
