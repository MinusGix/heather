---
title: Infer a record type's parameter that is a constant family
status: open
labels: [elaborator,inference,records]
area: language
created: 2026-11-10
updated: 2026-11-10
---

An implicit argument that is a parameter of a record type is not inferred
from an argument of that type when the parameter is a function and the actual
is a constant family: the record's fields apply it, the application reduces
away, and nothing is left to read the parameter back from. A later implicit
whose type mentions it fails with it.

## Reproduction

```
record R<P>(C: P → Type, ax: (a: P) → C(a) → Nat) { f: (a: P, k: C(a)) → ax(a, k) = ax(a, k) }
fn R::g<P>({C: P → Type}, {ax: (a: P) → C(a) → Nat}, r: R<P>(C, ax)) → Nat { 0 }
fn pick(a: Nat, k: Bool) → Nat { 0 }
fn mk() → R<Nat>(λ (a: Nat) => Bool, pick) { R(λ a k => refl) }
fn use1() → Nat { R::g(mk()) }       // refused: could not infer the implicit argument `C`
fn use2<P>(C: P → Type, ax: (a: P) → C(a) → Nat, r: R<P>(C, ax)) → Nat { R::g(r) }   // accepted
```

With a family that does not reduce away (`λ a => Big(a)` for a `fn Big`, or
`Big` itself) the call is accepted. The cause is the one
[[implicit-from-record-parameter-type]] found: a record type has no head to
match, it lowers inline to its Σ tower, so parameters are recovered from
field types only.

## Where it bit

`FormalPoint<QInterval>(QInterval::Le, λ a => RealAxiom, RealAxiom::open, in)`
(lib/std/locale/real_point.hthr): the real line's axiom type does not depend
on the interval. `FormalPoint::point`, `in_open` and `in_cover`
(lib/std/locale/presentation.hthr) take the presentation explicitly because
of it.

## Scope

- Keep a record type's arguments recoverable where it is used as an
  argument's type: either a spelled head carried beside the lowered tower
  for unification, or the declared type of the argument read before its
  whnf.
- Then make the presentation implicit in `FormalPoint::point` and friends.
