---
title: "Indexed finitary families: fording indices over Wf"
status: open
labels: [frontend,elaboration,inductives,design]
created: 2026-07-26
updated: 2026-07-26
---

`inductive Vec<A> : Nat -> Ty { Nil : Vec<A>(0), Cons(n: Nat, x: A, xs: Vec<A>(n)) : Vec<A>(Succ(n)) }`
— a declaration whose type is a *family*, with the index fixed per
constructor. Today the surface has none, and `Vec`/`[T; k]` is instead a
**built-in `TyKind`** (`crates/syntax/src/ast.rs:156`) with literal-only
lengths, no eliminator (`docs/container-proofs.md`: "the SURFACE cannot
eliminate a vector"), and a `VecLit` expression form to match. That is a
special feature standing in for a language feature.

## It also settles a live contradiction

[[kernel-v1-extensions]] still says inductive families come from **indexed
W**. [[frontend-roadmap]] flagged (2026-07-26) that the branching argument
applies verbatim — β on open children is what sank plain `W` for first-order
data — so indexed *finitary* families should ford over `Wf`, consistent with
[[inductive-compiler]]'s own scope note that indices are "the same machinery,
not a fourth tier". The roadmap's words: "that contradiction should be
resolved before a typed IR is designed." This issue is where it gets
resolved, in a scheme doc, with the two paths compared rather than assumed.

Evidence in hand for the comparison: `crates/kernel/tests/acc.rs` +
`docs/acc-via-w.md` are a worked indexed-container fording over plain `W`
(root label + a code-valued coherence predicate + an `Id` on the index), and
they show what the `Id`-transport cost looks like in practice. The finitary
version over `Wf` should be able to do better, because the arity is data and
`Vec`/`Fin` are already formers.

## Why it is worth doing before the IR, not with it

A typed IR is the motivating consumer ([[ir-simulate-design]],
[[datarepr-separation]]), but the feature is not IR-specific: `Vec`, `Fin`,
bounded indexing, and anything with a well-typedness invariant in its type
want it, and the mathematics side wants it as much as the compiler side.
Doing it *for* the IR would bake IR-shaped assumptions into the general
machinery.

## Scope notes

- **Fording**, per [[inductive-compiler]]: constructor results carry `Id`
  equations on the index. The known cost is that a constructor's equation
  must be *discharged* at every use, so the round should measure how much
  `Id`-transport survives into ordinary code and whether the tier-1
  computation properties (β on open children, which route C was chosen for)
  hold at an indexed declaration.
- Depends on [[surface-polymorphism]] for the parameter half — `Vec<A>` is
  parametric *and* indexed, and conflating parameters with indices is the
  classic mistake. State the distinction in the scheme.
- Retiring `TyKind::Vec`/`ExprKind::VecLit` in favour of a declared family is
  the acceptance criterion that makes this a de-magicking round rather than
  an addition. Check what the container rounds depend on
  (`docs/container-fields.md`, `docs/container-proofs.md`,
  [[nested-inductives-container-fields]]) before promising it.
- `Fin`-indexed elimination at the surface is the other half of "the surface
  cannot eliminate a vector"; decide whether it comes with this round or
  after.
