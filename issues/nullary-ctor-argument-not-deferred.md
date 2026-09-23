---
title: A bare `Nil` argument before the argument that pins its type is refused: add it to per-call deferral
status: open
labels: [frontend,elaboration,inference,ergonomics]
created: 2026-09-23
updated: 2026-09-23
---

Found 2026-09-23 by the receiver-first stdlib. `mconcat` now takes the list
first (`fn mconcat<A: Monoid(op)>(self xs: List<A>, op: A → A → A) → A`), and
`mconcat(Nil, o)` stopped elaborating where the old `mconcat(o, Nil)` did.
`crates/elab/tests/lib_algebra.rs` works around it with `Nil<A>`.

## Repro

```heather
import list;
fn first_then<A>(self xs: List<A>, d: A) → A { match xs { Nil => d, Cons(h, _) => h } }
fn then_first<A>(d: A, xs: List<A>) → A { match xs { Nil => d, Cons(h, _) => h } }

fn ok_checked() → Nat { first_then(Nil, 3) }                // refused
theorem p_later(): first_then(Nil, 3) = 3 { refl }            // refused
theorem p_earlier(): then_first(3, Nil) = 3 { refl }          // checks
theorem p_receiver(n: Nat): Nil.first_then(n) = n { refl }    // refused
```

All three refusals are `constructor.rs`'s "cannot infer the type argument `A`
of `List` here — no argument of `Nil` determines it". Only the order of the
explicit arguments differs from the one that checks. Even `ok_checked`, where
the declared result `Nat` pins `A`, is refused.

## Reading (a hypothesis, not yet checked with an instrument)

Per-call postponement ([[elab-unifier-completeness]], 2026-08-06) defers a
fixed set of checking-only explicit-argument shapes: holes, `refl`, vector
literals, unannotated lambdas, and bare references to polymorphic globals.
A bare nullary constructor of a parameterized type, like `Nil` or `None`,
whose own arguments cannot determine the parameters, is not in that set. So
it is elaborated in inference mode at a meta-bearing domain and fails before
expected-type solving or a later argument can pin `A`. The likely fix is to
add that shape to the deferrable set: a constructor application where no
child argument determines the type parameters, the case `ctor_from_child`
cannot handle. Receiver position (`Nil.first_then(n)`) is a separate question:
dispatch needs the receiver's head, which `Nil` does give (`List`), but
the instantiation still has to wait.

## Also a diagnostics dent

The message's first "way out" is "an argument of a declaration that expects
one". That describes this call exactly, so the advice is wrong here. Whatever
the fix is, it should not tell the reader to do what they already did.

## Done when

- The four repro lines check, or the receiver one is pinned as a deliberate
  refusal with a message that says why.
- The `Nil<A>` in `lib_algebra.rs`'s `slow_acceptance_the_library_projects_from_its_types`
  goes back to `Nil`.
- There is a test over the testing-generated-terms axes:
  - a neutral element type as well as `Nat`;
  - a checking position as well as an inference one;
  - `None` as well as `Nil`;
  - a negative control where nothing ever pins `A`, which must still be refused.
