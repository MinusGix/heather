---
title: Type parameters on fn/theorem, and inductives that are actually parametric
status: open
labels: [frontend,elaboration,design]
created: 2026-07-26
updated: 2026-07-26
---

**You cannot write `map`.** `Decl` carries `params: Vec<Param>` and no type
parameters (`crates/syntax/src/ast.rs:71`), so there is no

```
fn map<A, B>(f: A -> B, xs: List<A>) -> List<B>
```

and no way to write one. An `inductive`'s type parameters exist, but they are
**monomorphized**: `InductiveDecl`'s own doc says `D<Nat>` and `D<Bool>` are
unrelated kernel types, and `Ctx.tyvars` (`crates/elab/src/lib.rs:2218`) is
described as "empty everywhere else: type parameters are monomorphized, so
they never survive into a kernel term". `List<A>` is not a type-level
function; it is a macro expanded per instantiation.

This is the largest expressiveness gap in the surface and the clearest case
of the general complaint: polymorphism today is a *special feature of the
elaborator* — a substitution table consulted while lowering one declaration —
rather than a feature of the language.

## Why it is not a kernel round

The kernel has had this since v0. Level-0 parametric polymorphism is
`Π(A : Ty 0). …` with fields at `El A` — Tarski-style, exactly how the
existing lowerings already decode codes. `Type::Pi`, `Type::Ty`, `Type::El`
and codes for every former are all present and exercised. So this is a pure
**surface + elaborator** round in the same low-risk class as
[[surface-function-types]]: no trusted-base change, no ch. 07 obligation.

What is *not* available below layer m, and stays out of scope, is **universe**
polymorphism — quantifying over the level. A function polymorphic over
`Ty 0` lives at level 1, which is fine; a function generic in `ℓ` is layer-m
work and belongs with the modal round.

## What it unblocks

- [[map-tabulate-convergence]] diagnoses itself with "the surface cannot
  state it … there is no polymorphism below layer m" — the bridging theorem
  wants a recursion on a length at an abstract element type.
- [[compile-typeclass-design]] / [[certifying-generator]]: a trait is a
  record of *generic* operations. Records ([[surface-records]]) are the other
  half; neither is much use alone.
- The mathematics side generally — an algebraic structure is generic by
  construction.
- [[indexed-families]] and any typed IR, both of which want `Vec<A>`-shaped
  declarations rather than one kernel type per instantiation.

## Sequencing: [[implicit-binders-in-function-types]] comes with it

Implicitness lives in `ParamMeta.implicit` on a *declaration*, looked up by
the callee's **name** (`params_of`/`implicit_mask`, `lib.rs:1303–1315`).
Without moving it onto the type, every polymorphic call spells its type
arguments positionally and every λ-bound callback stays fully explicit —
technically complete, practically unusable. That issue is filed as
ergonomics; alongside this one it is structural, and the two should land
together.

## Open questions for the scheme doc

1. **Does an `inductive`'s parameter become a real Π, or stay monomorphized
   with polymorphism only on `fn`?** Real parameters mean the lowering emits
   a code-valued function `λ(A : Ty 0). ⌜…⌝` and every constructor and
   recursor gains a parameter; monomorphized-inductives-plus-polymorphic-
   functions is a smaller step, but leaves `map` unable to *return* a
   `List<B>` built from a parameter. Probably the whole thing — and the cost
   lands in the tier-0/1 generators, not in the type system.
2. **Where do type variables live in `TyKind`?** Today `Named { name, args }`
   is the only nameable type form; a bound type variable would be a `Named`
   with no args resolving to a local binder rather than a declaration. Cheap,
   but it makes name resolution three-namespaced in type position.
3. **Inference boundary.** `map(f, xs)` must not need `<Nat, Bool>` written;
   that is the implicit-binder machinery plus pattern unification
   ([[elab-unifier-completeness]]). The scheme should say exactly which
   inference problems it solves and which it rejects with a message.
4. Interaction with the guard/self-call machinery ([[match-recursion]]) and
   with [[dependent-field-injectivity]]'s constant-motive trick, both of
   which assume closed field types today.
5. Whether `theorem` gets the same treatment as `fn` in one go. It should —
   a generic lemma is the point — but theorems are Ψ-globals and `fn`s are
   inlined, so the two lowerings differ.
