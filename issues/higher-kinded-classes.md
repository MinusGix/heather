---
title: Classes over a type constructor: Bind<M: Type → Type>, with the unifier's ?M(A) = F<A>
status: closed
labels: [design,elaboration,traits,unification]
area: language
milestone: [lang-sequencing]
created: 2026-10-31
updated: 2026-10-31
---

Round R2a of `docs/sequencing-surface-design.md` (§2.1, §12): classes whose
carrier is a type constructor, so `Bind<M>`/`Pure<M>` (and later functors and
traversals) can be stated. Minus, 2026-10-31, on PR #313: a `Monad` Heather
cannot express is something to fix in Heather.

## What already works (probe P1 of the note)

- A value-parameter inductive is a constructor: `inductive Box(A: Type)`
  passes as `M: Type → Type`.
- `λ (A: Type) => Option<A>` is a constructor value.
- A record over `M: Type → Type` is a dictionary: generic code over it
  computes by `refl`.

## Scope: three pieces

1. **Unifier**: solve `?M(Nat) =?= Option<Nat>` and `?M(Nat) =?= Box(Nat)`
   by the first-order approximation (head plus leading arguments, abstracting
   the last), as Lean and Haskell do. Today `pick({M: Type → Type}, x:
   M(Nat))` at either gives "could not infer the implicit argument `M`".
   State what happens for a carrier whose varying argument is not the last
   (`Result<A, E>`).
2. **A bare generic name as a constructor**: `Option` at a `Type → Type`
   position η-expands to `λ A => Option<A>`. Today: "`Option` cannot be used
   here".
3. **Classes over a constructor**: `class Bind<M: Type → Type> { … }`
   parses, an instance `instance Bind<Option> { … }` registers under the
   resolved head key, and `:= infer` / `requires` resolve it from a goal
   `Bind<?M>` once 1 has solved `?M`. Today the class syntax does not
   parse, `class Monad(M: Type → Type)` is refused for lacking a carrier,
   and a dummy carrier leaves the index unpinned.

## Done when

`class Bind<M: Type → Type>` has instances at `Option` and `Tac`, and a
generic `twice({M: Type → Type}, x: M(Nat), b: Bind<M> := infer)` resolves at
both and computes by `refl`. Refusals name their reason: an ambiguous
`?M`, and a constructor with no instance.

## What it assumes from elsewhere

- **[[sequencing-surface-design]]** owns the classes' shape (`Bind`, `Pure`, no laws as fields).
- **[[binding-statements]]** is the first customer.

## Log

- 2026-10-31: 2026-10-31: Decide [[parametric-type-families]] first: if <A> parameters become kernel families, pieces 1-2 here shrink or disappear and this round becomes its first step.
- 2026-10-31: Landed without a kernel change (docs/higher-kinded-classes-design.md). Piece 2: a bare generic name at a Type → Type position is D#tycode_fn^δ (a λ for tier 2). Piece 1: an applied meta takes the respelled subject's head plus leading arguments, and a type with no code function (Tac) is matched through a computed template; the last argument is the abstracted one, so Result abstracts its error type ([[class-instance-at-lambda-carrier]]). Piece 3: class Bind<M: Type → Type> lowers to record Bind(M: Type → Type); instances at Option and Tac resolve and twice computes by refl at both (lib/_tests/std/core/type_constructor_tests.hthr). Follow-ups: [[class-instance-at-lambda-carrier]], [[tier2-type-code-functions]].
