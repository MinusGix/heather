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

## Log

- 2026-07-26: Sequenced behind [[surface-function-types]] (roadmap item 9, after 8). The design fork this issue names — 'an indexed accessor (Fin n -> D, which the surface has no function type for) or a fold' — is decided by that round rather than within this one: with function values the fold is an ordinary library function taking a lambda, and the arm binder needs no special-form eliminator. Without them the only routes are (a) a 'fold' syntactic form sitting next to match, to be deleted as soon as lambdas land, or (b) matching the container by its length and pushing the tail recursion into an auxiliary, which makes it MUTUAL recursion with the function recursing on D and so needs mutual declarations plus cross-function termination checking — a bigger round than function types and less reusable. So this issue gets smaller by waiting. Unaffected by the wait and still this issue's own work: the container TyKind (which must be the kernel's Vec, not a user-declared List — that is the whole §8.1 argument, since routing through List stops beta firing on open children), vector literals for construction, and how a constructor argument's length reaches the shape.
- 2026-07-26: PHASE 1 LANDED: docs/container-fields.md, 11 tests across crates/elab/tests/{container_fields,vector_types}.rs, workspace at 390. The design: the length is an ORDINARY PAYLOAD FIELD and the container is a vector at that length — 'inductive Rose { Node(label: Nat, len: Nat, kids: [Rose; len]) }'. So the shape is unchanged, the arity term (which Wf has always allowed to be a term with the shape free) projects 'len' out of the shape, and the children tuple's tail IS the container. No List, no conversion between a user container and the kernel's Vec, and therefore none of §8.1's beta-on-open-subterms cost — the container in the source is the Vec in the kernel. Surface additions: '[T; n]' as a primitive indexed type (kernel Type::Vec directly, no fording) and '[a, b]' literals, checking-only. Lowering: FieldKind is now three-way (Payload/Plain/Container), the arity is Succ^k(len) with tier 1's literal being the len-absent instance of the same formula, and an arm binds the container as 'snd^k cs' — a real vector value, not an accessor or a fold-only opaque. THE FINDING, docs §9.1: the classification predicate 'recursive' was computed from arity(), which now counts only PLAIN children, so a container-only constructor made Rose classify as non-recursive and its children were SILENTLY DISCARDED. Every positive test passed against that broken encoding — construction, match, round-trip and no-confusion all work on a type with a field missing, because dropping a field makes a smaller type and nothing that only builds and projects can tell. The negative control 'Node(0,1,[a]) = Node(0,1,[b]) by refl must be REJECTED' is what caught it. Third time in this codebase a live defect was invisible to every positive test; the lesson is not 'more tests' but that a positive test cannot distinguish a type from a quotient of it. Deferred with reasons: recursion into the children (phase 2 — map/fold plus the self-call over a container, designed in §4.2), proofs by induction over a container (phase 3, genuinely harder, §4.3), and 'inj' at a container field, which is a dependent-field problem identical to tier 0 §6.2's and should be lifted with it.
- 2026-07-26: PHASE 2 LANDED: recursion into a container's children — 'Rose' is programmable, not merely declarable. crates/elab/tests/container_recursion.rs (6 tests) plus 7 kernel-level tests on the schemas; workspace at 403. What landed: three elim_Nat-on-the-length schemas in crates/elab/src/vec.rs (map, fold, tabulate — Vec reduces on its length, so a vector of neutral length cannot be projected and a Pi-over-the-vector motive is the only shape that works), the surface forms 'xs.map(f)'/'xs.fold(z, f)' as builtins, and a ContainerIh on GuardKind::Wf so a self-call can find its container. The acceptance is 'fn size(r: Rose) -> Nat' via 'kids.map(size).fold(0, add)'. THE DESIGN POINT: 'kids.map(size)' applies 'size : Rose -> Nat' to 'kids : [Rose; len]' — the types do not line up under any ordinary rule and are not meant to. It is the induction hypothesis, which the eliminator hands over as an index function 'Pi(i : Fin n). M' and tabulate turns into data; it is recognized syntactically and elaborates to nothing else. Letting 'size' be an ordinary value passed to a real map cannot work, because there is no fixpoint: the self-name is not a value, it exists only as the eliminator's ih ([[match-recursion]]'s design, not an accident). FINDINGS (docs §10): (1) map and fold both had the step's lambda domain as Vec(A; k) where the step proves M(S k), so it must be Vec(A; S k) — caught in seconds because the schemas were kernel-tested BEFORE any surface syntax reached them; through three layers of elaboration it would have been an opaque NotConvertible on a Rose program. (2) The motive-constancy check needs no occurrence traversal: substituting Zero and weakening back is the identity exactly when the variable did not occur, so vec::strengthen is two existing subst.rs operations rather than a fourth hand-written walk over the term grammar. (3) A mixed constructor offsets the container's indices by the plain-child count, pinned with an ASYMMETRIC tree since a symmetric one cannot catch an off-by-one. Phase 3 (proofs by induction over a container) is now a diagnostic naming §4.3 rather than a silence.
