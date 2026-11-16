---
title: A class instance at a λ type constructor (a Result monad over its value)
status: closed
labels: [design,elaboration,traits,unification]
area: language
milestone: [lang-sequencing]
created: 2026-10-31
updated: 2026-11-02
---

A class instance whose carrier is a **λ** constructor — the shape a `Result`
monad over its value type needs — is refused at the declaration today
(`docs/language/classes/higher-kinded-classes-design.md` §5 item 3):

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

## Log

- 2026-11-01: Binding statements landed (docs/language/sequencing-surface-design.md §13): the Result, Parser and ITree carriers are the customers this issue now blocks; the parser-combinator port waits here.
- 2026-11-02: Design investigation (docs/language/classes/lambda-carrier-instances-design.md, proposed). Probes on c80799c: Parser needs only partial-application carriers (`Parser<T>`, its slot is already last); CoTree<R>(E) fails even first-order, so no reorder reaches ITree; a named constructor (`ResultE(E)`) declares today and resolves when the value is spelled through it. Seven routes compared; recommended: partial-application carriers first, then carriers chosen by candidates (unique fit commits, several refuse, none falls back), named constructors for headless carriers, keep `Result<A, E>`. Waiting on Minus's choice.
- 2026-11-02: Minus chose route 5 (the type declares its varying slot). Built: `inductive Result<A, E> varies A`, partial-application carriers (`Bind<Either2<E>>`), and λ carriers checked against the declared slot (`instance<E> Bind<λ (A: Type) => Result<A, E>>` in result.hthr). `twice` and binding statements compute over Result. Closed. CoTree/ITree still need `constructor_spelling` to learn codata and value parameters; that is filed as issues/codata-type-constructor-carrier.md.
