---
title: A generic class lemma instantiated at a Wf-lowered carrier exhausts conversion fuel
status: closed
labels: [kernel,conversion,performance,elaboration,traits]
created: 2026-08-07
updated: 2026-08-10
---

Found by the traits **library adoption** round (2026-08-07), which is what a
dogfooding corpus is for: `lib/std/algebra/algebra.hthr` can register
`instance<A> Monoid<List<A>>` and *use* it freely, but it cannot state the
class's own one-line lemma at a list carrier.

```heather
theorem mconcat_single<A> requires m: Monoid<A> (x: A): mconcat(Cons(x, Nil)) = x {
    m.unit_r(x)
}
theorem at_list<A>(xs: List<A>): concat(Cons(xs, Nil)) = xs { mconcat_single(xs) }
//                                                            ^ kernel: OutOfFuel
```

The failure is fast (0.38s to burn the whole 2^20 `DEFAULT_FUEL`), so it looks
more like a conversion that does not converge than like a workload that is
merely large.

## The reproducer, minimized

Twenty lines, no traits-specific machinery beyond the class itself, and it does
**not** need the resolver: a *declared, monomorphic* instance reproduces it.

```heather
import list;
import nat;
class MonoidX<A> {
    unit: A,
    op: A -> A -> A,
    assoc: (x: A) -> (y: A) -> (z: A) -> op(op(x, y), z) = op(x, op(y, z)),
    unit_l: (x: A) -> op(unit, x) = x,
    unit_r: (x: A) -> op(x, unit) = x,
}
instance MonoidX<List<Nat>> {
    unit := Nil,
    op := append,
    assoc := append_assoc,
    unit_l := λ (xs: List<Nat>) => refl,
    unit_r := append_nil,
}
fn mcx<A> requires m: MonoidX<A> (xs: List<A>) -> A {
    match xs { Nil => m.unit, Cons(h, t) => m.op(h, mcx(t)) }
}
theorem mcx_single<A> requires m: MonoidX<A> (x: A): mcx(Cons(x, Nil)) = x { m.unit_r(x) }
theorem at_list(xs: List<Nat>): List::MonoidX.op(xs, List::MonoidX.unit) = xs { mcx_single(xs) }
```

## What the probes place, and what they exonerate

Each of these is the same file with one thing changed (all times: release
`heather check`, ulimit-wrapped).

| variant | result |
|---|---|
| the file above | **OutOfFuel**, 0.38s |
| generic instance `instance<E> MonoidX<List<E>>` instead of the monomorphic one | same failure |
| statement written with `mcx(...)`, proof written as the direct projection `List::MonoidX.unit_r(xs)` | **ok**, 0.32s |
| statement written directly, proof `mcx_single(xs)` (the row above, reversed) | **OutOfFuel** |
| drop `assoc` from the class | ok, 0.21s |
| drop `unit_l` from the class | ok, 0.47s |
| carrier `Nat` instead of `List<Nat>`, all five fields | ok |
| the same class at `List` with the lemma stated as `m.op(x, m.unit) = x` (no generic `fn` in the statement), plus three padding fields | ok, 0.22s |

So: **not** the resolver (a declared instance does it), **not** the derivation
(the generic instance behaves identically), **not** the dictionary's size alone
(the direct projection is cheap at the same dictionary), and **not** `Wf` alone
(the same lemma at `Nat` is fine). What is left is the combination —
*instantiating a generic theorem whose statement mentions a generic recursive
`fn`, at a concrete dictionary over a `Wf`-lowered carrier* — where the goal
side and the given side have to be brought together by unfolding `mcx` at the
substituted dictionary.

The suspicion worth checking first is that the class value is a Σ-tuple and
each projection re-forces the tuple, so `mcx`'s two projections under a `Wf`
recursion multiply rather than add: dropping either heavy field alone is fine,
and keeping both is not.

## Why it matters beyond one theorem

This is the shape of *every* algebraic library: prove the law once against the
class, use it at each carrier. If a container carrier cannot host the generic
lemma, the class layer buys the abstraction for programs but not for proofs at
exactly the carriers that most want it. `lib/std/algebra/algebra.hthr` records the gap
in place (the missing `concat_single`) rather than working around it.

## What it assumes from elsewhere

- **[[traits]]** owns the class/instance semantics. Assumed here: only that an
  instance value is an ordinary record and a `requires` binder an ordinary
  parameter — both of which the probes above confirm by removing the resolver
  from the picture entirely.
- **[[whnf-sharing-term-growth]]** owns the unforced-redex growth story;
  whether this is an instance of it is the first thing to check.

## Log

- 2026-08-10: LANDED: this was not repeated evaluation or the old whnf term-growth exponent. Instrumentation placed 474,701 of the exhausted budget units at recursive `Conv::ty` entries on shared type children; a general term-child identity shortcut had no effect. Conversion now accepts type children by scoped closure identity (same pointer, `home`, and `sat`) after spending one comparison unit. The syntax oracle uses pointer identity too. The capped release reproducer goes from OutOfFuel at ~0.37s to success at ~0.14s; `concat_single<A>` is restored in std/algebra, a scope-mismatch unit control pins the soundness boundary, differential/kernel/full workspace suites are green.
