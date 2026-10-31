---
title: A class instance at a λ type constructor (a Result monad over its value)
status: open
labels: [design,elaboration,traits,unification]
area: language
milestone: [lang-sequencing]
created: 2026-10-31
updated: 2026-10-31
---

A class instance whose carrier is a **λ** constructor — the shape a `Result`
monad over its value type needs — is refused at the declaration today
(`docs/higher-kinded-classes-design.md` §5 item 3):

```heather
instance<E> Bind<λ (A: Type) => Result<A, E>> { … }
// error: the type parameter `E` does not occur in the head `Bind<_>`
```

Two things block it: the binder-occurrence check does not look inside a λ
carrier, and a λ has no head for the canonical name `{Head}::{Class}` or the
registry key.

Even with the declaration accepted, a use site has to pick `?M := λ A =>
Result<A, E>` from `?M(Nat) ≟ Result<Nat, Bool>`. The unifier's first-order
approximation abstracts the **last** argument and so picks `Result<Nat, _>`.
Abstracting a chosen argument is not first-order any more.

## Options

1. **Put the varying argument last**: `Result<E, A>`, as Haskell's
   `Either e a` does. The approximation then gives `?M := Result<E>`
   (head plus leading argument), and `instance<E> Bind<Result<E>>` needs a
   carrier spelled as a *partial* application, which piece 2 refuses today
   (a bare name only). This option touches every `Result` use in the library.
2. **λ-carrier instances**: accept the declaration (occurrence check
   through the λ, a canonical name from the λ body's head), and at a use
   site try each λ-carrier instance by unifying its body against the
   subject. That is resolution choosing `?M` by candidates, not
   unification guessing it.
3. **Name the constructor**: `fn ResultE(E: Type) → Type → Type { λ A =>
   Result<A, E> }` and instances at `ResultE(E)`. Same use-site question as 2.

## Done when

`twice` (the probe in `lib/_tests/std/core/type_constructor_tests.hthr`)
computes at a `Result` value through a `Bind` instance, and the chosen
route is recorded in the design note.
