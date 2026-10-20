---
title: Slot sections under a call are refused at a meta-bearing parameter
status: open
labels: [frontend,elaboration,ergonomics]
area: language
created: 2026-10-08
updated: 2026-10-08
---

A section whose slot sits under a call is refused when it is passed at a
parameter whose domain still has unsolved implicits:

```heather
fn apply_to<A, B>(f: Cell<A> -> B, c: Cell<A>) -> B { f(c) }
fn idn(n: Nat) -> Nat { n }
fn t<A>(c: Cell<A>) -> Nat { apply_to(idn(·.count), c) }
error: an argument slot needs an enclosing checking position with a function type
```

`apply_to(λ s => idn(s.count), c)` is accepted: an unannotated lambda is a
checking-only argument (`is_checking_only`), so it waits for `c` to solve
`A`. A projection section (`apply_to(·.count, c)`) waits too: when its
inference escapes at a domain that is structurally a function type, the
call is re-planned with it deferred (`apply_implicit`'s restart,
[[field-projection-sections]]). That restart is limited to projection
sections, so a bare `·` and a slot under a call still escape here. For
`idn(·.count)` the escape then reaches a boundary with no function type and
is refused. Inferred, not separately probed on master: the same holds for
`idn(·)`.

Widening the restart to every escaping argument at a function-typed domain
would follow the ownership rule (the parameter is the smallest
function-typed checking position), but it also changes what a bare `·`
means at a generic function parameter, where today it escapes to the
enclosing section (`apply(·, 3)` at `(Nat -> Nat) -> Nat`). That change
needs its own look at the library.

## What it assumes from elsewhere

- **[[argument-slot-sections]]** owns `·` and the ownership probe. Assumed
  here: only that the smallest function-typed checking position owns a slot.
