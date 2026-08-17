---
title: "A record's type argument does not infer from a function-typed value parameter"
status: closed
labels: [frontend,elaboration,inference,stdlib]
created: 2026-08-16
updated: 2026-08-16
---

`lib/std/logic.hthr`'s existential is

```heather
record Exists<A>(P: A -> Type) { witness: A, proof: P(witness) }
```

and a *statement* using it has to spell `A`, even though the predicate
determines it:

```heather
fn Even(n: Nat) -> Type { Exists(λ (k: Nat) => add(k, k) = n) }
//                        ^ `Exists` takes 1 type argument(s), found 0
fn Even(n: Nat) -> Type { Exists<Nat>(λ (k: Nat) => add(k, k) = n) }   // ok
```

The information is right there: the lambda's binder is annotated `Nat`, and
the value parameter's declared type is `A -> Type`, so `A := Nat` is a
first-order match. Nothing exotic is being asked for — no higher-order
unification, no inversion — because the argument's type is *given* by the
writer rather than being synthesized from a body.

Introduction already works: `Exists(2, refl)` at an expected `Even(4)` takes
`A` from the expected type. So the gap is specifically **type arguments
inferred from a value argument's type**, in the direction the expected type
cannot supply.

Pinned at `crates/elab/tests/logic.rs`,
`exists_does_not_infer_its_type_argument` — a `bad()` today, written so that
closing this issue surfaces as a test that must change rather than as a silent
improvement.

## Scope

The general shape is "a declaration's leading type parameters, solved against
the *types* of the explicit value arguments before checking them", which is
ordinary first-order argument-directed inference. `Exists` is the first
library customer; every record with a function-typed value parameter is the
same case.

Not in scope: inferring from the *body* of an unannotated lambda
(`Exists(λ k => …)`), which is a genuinely harder question and has no library
customer today.

## Why it is not urgent, and why it should still be filed

The `∃` notation ([[std-logic-module]], landed 2026-08-16) hides it at every
site that uses the sugar: `∃ k: Nat, P` supplies `<Nat>` from the binder's own
annotation, which is exactly the information the inference would have
recovered. So the library reads correctly today and the workaround is not
visible in it.

That is also the argument for filing it rather than letting the sugar close
the question: the sugar covers the *notation*, not the *declaration form*, and
the next value-parameterized record with a function parameter will meet this
again with no notation to hide behind.

## What it assumes from elsewhere

- **[[surface-existential]]** owns the record value-parameter form (the
  design record is `docs/surface-value-parameters.md`). Assumed here: only
  that it landed and that `Exists` is a legal declaration in it.
- **[[type-arg-inference-through-index]]** owns type-argument inference where
  an *index* is what carries the information. Assumed here: only that its
  subject is the indexed case; check on scheduling whether these are one fix
  or two, since the answer decides whether this issue survives.
- **[[elab-unifier-completeness]]** owns the unifier's reach. Assumed here:
  nothing — this case is first-order and should not need any of it.

## Log

- 2026-08-16: Filed from the [[std-logic-module]] round, which met it while
  writing the generic existential and worked around it in the notation. Worth
  recording as the round's own judgement: this is the one place where the
  direct spelling is clearly better than what the language gives, so the sugar
  is covering a gap rather than expressing a preference.
- 2026-08-16: FIXED (2026-08-16), same day. `Exists(λ (k: Nat) => add(k, k) = n)` checks; `Exists<Nat>(…)` still writes and the two are the SAME type, pinned by passing one where the other is expected rather than by checking each on its own. Mechanism: `Elaborator::valparam_targs` (crates/elab/src/inductive.rs), consulted by `try_valparam_ty` when the type-argument list is omitted ENTIRELY. Each value argument is inferred and its type matched against the parameter's DECLARED SURFACE TYPE by `match_targs`, which reads a solution wherever the declared side is exactly a type parameter — so `A -> Type` meets the inferred `Π(Nat). Ty 0` and `A := Nat` falls out of the domains. Three boundaries, each chosen rather than fallen into. (1) FIRST-ORDER AND ONE-SIDED, on the doctrine `infer_ctor` already states for constructors: the declared side is a skeleton with the parameter names as holes, the actual side is inspected only where the skeleton has structure, and anything deeper is [[elab-unifier-completeness]]'s. (2) DOMAIN-ONLY through an arrow. A solution read out of a CODOMAIN would have been extracted from under the binder, where it may mention the bound variable and could not be lifted out soundly — `A -> Type` solves from the domain, so the restriction costs nothing today and cannot become wrong later. (3) A PARTIAL list is still an arity error: filling some type arguments and inferring the rest is a different feature and nothing asks for it. An argument that fails to infer is not an error here either — it solves nothing, and the unsolved parameter reports by NAME ("cannot infer the type argument `A`") rather than by arity, which is the message the old "takes 1 type argument(s), found 0" should have been. This does NOT close the general question the issue's scope section describes (a declaration's leading type parameters solved against every explicit value argument, in general): what landed is the narrow reading, sized to the one library customer. Nothing is owed — the general case has no customer and would be unification. Tests: crates/elab/tests/logic.rs `exists_infers_its_type_argument_from_the_predicate` (both spellings, agreeing; the ∃ sugar beside them; an OPEN predicate at another carrier so nothing is hardcoded to Nat), `an_undetermined_type_argument_is_still_refused` (a phantom parameter, refused by name, with the written form as the way out), `a_partial_type_argument_list_is_still_an_arity_error`. Docs: docs/logic-connectives-design.md §6.2. CLOSING.
