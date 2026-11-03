---
title: The applied-meta approximation's wrong guess surfaces as a misleading type error
status: open
labels: [diagnostics,elaboration,unification]
area: language
milestone: [lang-sequencing]
created: 2026-11-02
updated: 2026-11-02
---

The first-order approximation for `?M(p̄) ≟ D<ā>` abstracts the **last**
argument (docs/higher-kinded-classes-design.md §3). When that is the wrong
slot, the user sees a consequence of the guess rather than the guess
(probed on `c80799c`, docs/lambda-carrier-instances-design.md §2):

```heather
fn pick({M: Type → Type}, x: M(Nat)) → M(Nat) { x }
fn r1(r: Result<Nat, Bool>) → Result<Nat, Bool> { pick(r) }
// error: this has type `Result<Nat, Bool>`, but `Result<Nat, Nat>` is expected here
```

and `twice(r)` reports "no instance for `Bind<Result>`", where the goal is
really `Bind<Result<Nat, ·>>`.

## Done when

The mismatch names the constructor it chose and that it abstracted the last
argument (with the `M := λ A => …` spelling to write instead), and a kinded
goal at a partial application displays its fixed arguments. Under
[[class-instance-at-lambda-carrier]]'s route 6 the class case changes, but
`pick` keeps the approximation, so the message is owed either way.

## Log

- 2026-11-02: docs/elaborator-principles-survey.md proposes taking this approximation last, as a named guess: [[unifier-guesses-postponed]].
