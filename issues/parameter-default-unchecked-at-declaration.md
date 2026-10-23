---
title: Check a parameter default at its declaration, not only at a call
status: open
labels: [frontend,elaboration,defaults]
area: language
created: 2026-10-23
updated: 2026-10-23
---

A default is elaborated only at a call that leaves it out
(docs/named-arguments-design.md §9.4), so a default no call uses is never
checked by anyone:

```heather
record P { a: Nat, h: a = 3 }
fn g(x: Nat := P(2, refl).a) -> Nat { x }   // accepted
fn h() -> Nat { g() }                       // refused here, by the kernel
```

This is the sibling of [[unused-let-value-unchecked]]: a written
expression that reaches the kernel only through a use. It is not the same
fix, because a default is open in the caller's context by design: `:= omega`
and `:= positivity` search the caller's hypotheses, and only a call
instantiates the earlier parameters it mentions.

A declaration-site check could elaborate a default that is not a tactic in
the declaration's own telescope (the earlier parameters as binders, which is
what `mentioned_parameters` already reads) and hand it to the gate, for
example as a side obligation of the function. Open questions: whether a
default that only typechecks at some instantiations should be legal at all
(today it is, and the call reports it), and how
[[default-kernel-failure-reported-at-declaration]]'s span rule interacts.
