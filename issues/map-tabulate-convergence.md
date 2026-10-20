---
title: map and tabulate do not converge at a neutral length
status: open
labels: [elab,vec,ir,design]
area: language
created: 2026-07-26
updated: 2026-07-26
---



`vec::map(f; xs)` and `vec::tabulate(n; λi. f (nth xs i))` denote the same
vector and are **not convertible** at a neutral length. Both are `elim_Nat`
schemas on the length, so at a neutral `n` neither reduces, and they are
structurally different terms: `map` walks the Σ-chain with `fst`/`snd`, while
`tabulate` builds from an index function.

Found while probing the phase-3 mixed case (`docs/container-proofs.md`), where
a fully explicit `@cong_add(…, rest.map(tt), …)` fails for exactly this reason:
inside a *theorem*'s arm the self-name is `same`, so `rest.map(tt)` elaborates
to a real `map` over the global `tt`, while the goal holds the `tabulate` that
`tt`'s own definition produced from its ih.

## Why it is not a bug in either schema

Neither is wrong; they are two normal forms for the same function, and no rule
relates them. The bridging fact

```
map(A; B; n; f; xs)  =  tabulate(B; n; λi. f (nth(A; n; xs; i)))
```

is a *theorem*, provable by `elim_Nat` on `n` (base: both `⟨⟩` at `Unit`; step:
pairing congruence, the same shape `vec::tab_cong` already has). The surface
cannot state it — that needs a recursion on a length, and there is no
polymorphism below layer m — so it would be a fourth schema in
`crates/elab/src/vec.rs`, not a library lemma.

## Why it does not bite yet, and when it will

Nothing today needs them to agree: the ih path never produces a real `map`, and
the phase-2/3 acceptances only ever compare a `tabulate` with a `tabulate`. It
bites the first time a program relates an **ordinary helper over a vector** to
the output of a container recursion — write `fn sum(n: Nat, xs: [Nat; n])` with
`xs.map(g)` in it, and try to prove anything connecting it to a `Rose`
recursion.

[[ir-simulate-design]] is the plausible first consumer: a `FunctionIR` is
first-order data with a vector of instructions, and `simulate` will both
recurse over the IR (tabulate, via the ih) and call helpers over the same
vector (map).

## Options, when it is time

1. **The bridging schema** (`map_is_tabulate`), stated above. Smallest, and it
   composes with `tab_cong` — but every use has to invoke it by hand, and the
   surface has no way to *name* a schema.
2. **Elaborate `map` to `tabulate`** and delete the `map` schema. One normal
   form, nothing to bridge; costs the `fst`/`snd` walk, which is the cheaper
   term on a *literal* length, and would want measuring first.
3. **Recognize the pattern at elaboration**, as phase 2 recognizes the self-call
   — narrow, and it does not help when the two spellings arrive from different
   declarations, which is the case that actually hurts.

Option 2 is the one that removes the problem rather than papering it; option 1
is the one that can land in an afternoon. Decide against a real consumer, not
in the abstract.

## Log

- 2026-07-26: Filed out of container-fields phase 3 ([[nested-inductives-container-fields]]). Not blocking that round: phase 3's acceptance never mixes the two spellings, and the failing probe was an artefact of writing endpoints explicitly rather than a limit of the lifting.
- 2026-07-26: Its stated blocker now has an issue: 'the surface cannot state it -- that needs a recursion on a length, and there is no polymorphism below layer m' is [[surface-polymorphism]], roadmap item 11. The bridging theorem is a generic statement over the element type, so it becomes writable (as a theorem, not a fourth schema) once type parameters exist on fn/theorem. Worth re-testing this issue's witness right after that round rather than treating the design options here as settled.
- 2026-07-26: Unblocked on the polymorphism side: [[surface-polymorphism]] landed, so a recursion on a length at an abstract element type is now stateable -- 'fn f<A>(n: Nat, xs: [A; n])' and a declared inductive at an open instantiation both elaborate. The bridging theorem itself has not been attempted.
