---
title: The surface story for mconcat: name (fold?), and whether it deserves syntax
status: open
labels: [design,library,ergonomics]
created: 2026-08-11
updated: 2026-08-11
---

Two user musings from the op-as round review (2026-08-11), filed before they
evaporate; both are naming/surface questions, neither blocks anything.

**The name.** `mconcat` is Haskell's word. `fold` is the obvious rename — the
operators tests already define a local `fold` of exactly this shape — but the
function is specifically the *monoid* fold (unit from the class, operation
tied to the constraint), not a general `foldr` with an explicit base. If a
general fold ever lands in `std/list`, the two need distinct names, and
`mconcat`'s ugliness is doing real work marking the monoid-ness. A rename
decision should say what the general fold will be called *first*.

**Syntax.** "Fold this list through its designated operation" is common enough
on lists to tempt dedicated syntax. Restraint has a good track record here
(designations stayed a table, no nomination rung was added), so the bar: what
would syntax buy over `mconcat(++, xss)` — which
[[bare-symbol-checking-carrier]] would already make read well? File the
concrete proposal here if one forms; until then this issue owns only the
question.

## What it assumes from elsewhere

- **[[bare-symbol-checking-carrier]]** owns symbol arguments in checking
  position. Assumed here: only that `mconcat(++, xss)` is its acceptance shape.
- **[[notation-extensibility]]** owns the lexicon; any syntax proposal here
  pays that issue's costs.

## Log

- 2026-08-11: bare-symbol-checking-carrier landed 2026-08-11: mconcat(++, xss), mconcat(||, bs), mconcat(&&, bs) are legal. As predicted, 'the operation must be spelled at every call site' is now weaker as an argument for computational functions and unchanged for lemmas. Not decided here.
