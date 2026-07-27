---
title: Type parameters on fn/theorem, and inductives that are actually parametric
status: closed
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

## Answers (2026-07-26, `docs/surface-polymorphism.md`)

The scheme answered all five, and three of them differently from the way this
issue framed them.

1. **Neither option.** An `inductive`'s parameters stay expanded per
   instantiation *and* `map` can return `List<B>` — because an instantiation
   may now be **open**. Inside `fn map<A, B>`, `List<B>` lowers to
   `⟦List<El B>⟧`, an ordinary kernel type with `B` free. No code-valued
   type-level function, no parameter on any constructor or recursor, and the
   cost this issue expected to land in the tier-0/1 generators does not
   exist. The premise that monomorphized-inductives leaves `map` unable to
   return a `List<B>` was wrong; what made it wrong is
   [[tyvar-scoping-in-lowered-fields]], landed the same day.
2. **No new `TyKind`.** A bound type variable is `Named { name, args: [] }`
   resolving through `Cx.tyvars`, which already maps a surface type name to a
   kernel type at a binding depth. Name resolution in type position does
   become three-namespaced, as predicted, but the machinery was written.
3. **Argument-driven, pattern-fragment only.** Solved from the *inferred
   types of the explicit arguments* by structural congruence plus one rule
   (`El ?A ≟ T ⇒ ?A := ⌜T⌝`), with depth tracking and a strengthening test.
   Rejected with a message: a parameter appearing only in the result type
   (`nil()`), an unannotated λ-argument, anything outside the fragment.
   `f<T, …>(…)` is the escape hatch and always works.
4. **The guard machinery needed no change**; type parameters are implicit, and
   `elab_self_call` already filters positions by implicitness.
5. **Yes, in one go, and it is not two lowerings.** `fn` and `theorem` share
   `elab_decl_inner` end to end; the split is four lines at the very end.

The sequencing claim in this issue was also wrong:
[[implicit-binders-in-function-types]] did **not** become structural. A type
parameter is a *declaration* parameter, so it is `ParamMeta.implicit` — where
implicitness already lives — and no polymorphic call spells its type
arguments positionally. What stays explicit is applying a polymorphic
function *value*, which is exactly the limitation
[[surface-function-types]] §5.3 already recorded.

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

## Log

- 2026-07-26: Scheme written: docs/surface-polymorphism.md (grammar, the El/Ty lowering, the inference rule with its depth/strengthening obligation, six interactions to observe, nine rejections with messages, a 19-item acceptance checklist). Three of the five open questions came back differently from the way this issue framed them, all recorded above: inductives need neither option (an open instantiation is enough, and map returns List<B> today), theorem needs no separate lowering, and implicit-binders-in-function-types does not become structural.
- 2026-07-26: IMPLEMENTED and green: 33 acceptance tests in crates/elab/tests/polymorphism.rs, workspace at 465 passing. Landed: Decl.tyvars parsed as fn/theorem name<A, B>; type parameters lowered as leading implicit binders at Ty 0 with a use decoding through El; ExprKind::TyApp with a speculative parse that backtracks cleanly against the lt operator; crates/elab/src/code.rs quoting a kernel Type to its code; unify_ty/unify_tm grown from Id-only to full congruence with binder-depth tracking, a strengthening test (drop the inner binders to a marker, reshift, compare -- no new traversal) and the El rule that makes a type argument inferable; an expression read as a type in a Ty l position, so @f(Nat, ...) works; and constructors at a written instantiation (Nil<Nat>). fn map<A, B>(f: A -> B, xs: List<A>) -> List<B> over a declared List now parses, elaborates, kernel-checks and computes -- the issue's headline. Two live PRE-EXISTING defects found by the headline test and fixed, neither about polymorphism: (1) a declaration could not be named after a built-in eliminator, because shadowed did not count the enclosing declaration's own name, so fn map's self-call took the vector-map path; (2) wf_branch projected a container's length in cx while its arguments were shifted into bcx -- invisible at a closed instantiation, and the axis-2 control that exposes it (Rose<A> at an open element type) WAS NOT WRITABLE until this round, which is now the sixth row of docs/testing-generated-terms.md. Three scheme corrections in docs/surface-polymorphism.md section 10: constructors need type application too, ty_atom's Ident-< early return swallows a type-applied call in type position (the discriminator is a following paren), and apply_explicit needed a parameter offset for goal hints. Limit found and filed rather than fixed: an implicit function parameter still cannot be inferred from an equation (cong_at declares but does not apply), which is elab-unifier-completeness.
- 2026-07-26: Prelude probe run 2026-07-26, before starting [[surface-records]]. Result: inference carries completely -- polymorphic sym/trans declare, kernel-check, and infer their carrier at Nat, at a declared Bool, through the method sugar and in a trans chain. Swapping the real prelude for polymorphic sym/trans gives 450 passed / 16 failed, and ALL 16 are '@'-spelled calls or 'calc' (which desugars to '@trans'); the single implicit-args failure is the one named explicit_override_still_available. So the round's inference is sufficient and the obstacle is a surface-semantics collision, filed as [[at-and-type-arguments]] with a recommendation ('@' and '<...>' as orthogonal knobs) that reverses this round's decision to reject '@f<...>'. Also confirmed: a polymorphic 'cong' works with 'f' EXPLICIT ('cong(Succ, p)' checks), so the prelude can generalize in full once '@' is settled -- only the f-implicit form needs [[elab-unifier-completeness]]. Prelude left monomorphic; nothing in the tree changed.
