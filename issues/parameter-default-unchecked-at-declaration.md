---
title: Check a parameter default at its declaration, not only at a call
status: closed
labels: [frontend,elaboration,defaults]
code: crates/elab/src/defaults.rs
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

## Resolution (2026-10-23)

docs/named-arguments-design.md §9.7. A default is checked at its
declaration as far as the declaration decides it
(`Elaborator::check_default_at_declaration`):

- A **discharge** (a goal-reading head: `omega`, `positivity`, `ring`,
  `decide`, `refl`, `by t`, …, or any `?`) is the call's alone, like
  `:= infer`.
- A **value** is elaborated in the telescope of the parameters before it and
  kernel-checked there: at the parameter's type, or, when that fails, at its
  own type provided a call could still change the fit (either type mentions
  an earlier parameter). The issue's `P(2, refl).a` is refused at `g`.

The open question is answered: a default that only fits some instantiations
stays legal when its own term is well-typed and the call can still decide
the fit (`zero: IsZero(n) := Holds`; lib's `nan: F.specials.has_nan().IsTrue()
:= trivial`, a `True` whose fit depends on `F`), and is refused when its own
term is ill-typed or its fit is fixed and wrong
(`b: Bool := 5`). On [[default-kernel-failure-reported-at-declaration]]: a
value's kernel failure that holds at every call is now the declaration's own
error, reported there; that issue keeps the discharges.

Tests: `crates/elab/tests/named_arguments.rs` §9.7 block (no call at all, a
theorem, a mentioning default, a fixed misfit, a call-dependent fit with a
bad subterm, a `refl` discharge, an open type), `positivity_tactic.rs`
(`a_tactic_inside_a_value_default_runs_at_the_declaration`; its `DEFAULTS`
are the uncalled `omega`/`positivity` discharges).

Record field defaults followed on 2026-10-24: [[field-default-unchecked-at-declaration]].
