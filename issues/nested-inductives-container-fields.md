---
title: Nested inductives: a children-container field type at the surface
status: open
labels: [frontend,elaboration,inductives,surface]
created: 2026-07-26
updated: 2026-07-26
---



Split out of [[wf-former]] phase 5, which delivered the branching tier-1
generator and deliberately did **not** deliver `Rose`. Full argument:
`docs/inductive-tier1-wf-lowering.md` §8.1; the correction it makes to
`docs/wf-former-design.md` §7 is the reason this is an issue rather than a
checklist item.

## The claim that needed correcting

The `Wf` design doc records `Rose { Node(A, List Rose) }` as "nearly free",
because `S = Σ(a : A). Nat` and `n = snd x` type it: the child list *is* the
`Vec` and its length is data in the shape. That is true, and it is a real
payoff of arity-as-a-term — the **type** costs nothing.

It says nothing about the **lowering** from a surface declaration whose field
type is a user-declared `List`, and that is where the cost is.

## Why it is not a generator tweak

The generator would have to identify the user's `List<Rose>` with the
kernel's `Vec^l(⟦Rose⟧; k)`. Both directions are *definable* — `Vec → List`
by `elim_Nat` on the length, `List → Σ(n : Nat). Vec` by `elim_Wf` on the
list — so this is not a typing problem. It is a computation problem:

- `Node(xs)` for a **neutral** `xs` would lower to
  `sup_f(⟨a, len xs⟩; toVec xs)`,
- so `match Node(xs) { Node(ys) ⇒ ys }` gives back `fromVec (toVec xs)`,
- which is convertible with `xs` only for a **canonical** `xs`.

β would stop firing on open subterms. That is exactly the property route C
was chosen for over the fording scheme
(`docs/branching-inductives-choice.md` §15), and a lowering that loses it is
not this tier.

## What would actually unblock it

Surface support for a **children-container field type**: a field a
declaration states *as* a vector of `D`, so that the container in the source
and the `Vec` in the kernel are the same object and no conversion appears.
That is a surface-language round, not a generator one:

- a new `TyKind` (the surface's type grammar is `Nat` / a named declaration /
  `=` today, with no container),
- what a `match` arm binds for such a field, and what one can *do* with it —
  the honest options are an indexed accessor (`Fin n → D`, which the surface
  has no function type for) or a fold, and that choice is the design work,
- how a constructor argument in that position is written, given that its
  length has to reach the shape.

Only then does the generator step become the small one the design doc
imagined.

## Related and still separate

Indexed families (ford by `Id`), mutual declarations, and polymorphic
containers (a surface gap of its own: the type grammar has no inhabitant
above level 0 to instantiate a parameter with, though the tier-1 lowering
takes its level from the shape throughout and assumes nothing). All three
are listed in `docs/inductive-tier1-wf-lowering.md` §8.
