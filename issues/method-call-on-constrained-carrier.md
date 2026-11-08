---
title: Dot calls on a constrained type-variable receiver find the class's members
status: open
labels: [frontend,elaboration,effects]
area: language
created: 2026-11-08
updated: 2026-11-08
---

A dot call on a receiver whose type is a type variable finds nothing:
`c.say(m)` with `c: C` and a constraint `d: Log<C> := infer` in scope is
"unbound name `say`", although `Log::say<C>(mut self c: C, …)` is declared
(probe in the appendix of `docs/effects-locality-design.md`, run on
`a6d30ca`). Member lookup goes by the head of the receiver's type, and a
variable has no head. So interface-generic effectful code writes
`c := Log::say(c, m).after` and loses the `mut self` threading that makes
the `Io` surface read as imperative code.

## Scope

- When the receiver's type is a type variable, look the member up among the
  owners that are classes constraining that variable in scope (instance
  arguments `d: K<C> := infer` and section constraints), as Rust finds trait
  methods on a generic and Haskell finds class methods.
- Ambiguity (two constraining classes owning the member) is refused with
  both candidates named.
- The `mut self` candidate marking and the declaring block's claim work as
  for a concrete receiver, so `c.say(m);` threads `c`.
- Probes: the note's `greet` written with dot calls, a negative control for
  an unconstrained variable, and the hot dot-call path unchanged for
  concrete receivers.

## What it assumes from elsewhere

- **[[effect-interfaces-over-carriers]]** is the customer.
