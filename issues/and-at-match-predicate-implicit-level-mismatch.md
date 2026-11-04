---
title: And against a match-defined predicate at an inferred implicit is refused by the kernel (LevelMismatch)
status: closed
labels: [frontend,elaboration,inference,defect]
area: language
created: 2026-10-30
updated: 2026-10-31
---

The elaborator accepts, and the kernel refuses with a bare `LevelMismatch`,
an `And(l, h)` passed for a parameter typed by a predicate defined by a
`match`, when an implicit that the predicate mentions is inferred (master
`ed998b0`):

```heather
import logic; import nat;

inductive Iv { B(lo: Nat, hi: Nat), W }

fn Iv::Has(self I: Iv, x: Nat) → Type { match I { B(lo, hi) => lo <= x ∧ x <= hi, W => True } }

theorem keepx(I: Iv, {x: Nat}, h: I.Has(x)): I.Has(x) { h }

// error: the kernel rejected `b1`: LevelMismatch
theorem b1(lo, hi, x: Nat, l: lo <= x, h: x <= hi): B(lo, hi).Has(x) { keepx(B(lo, hi), And(l, h)) }
```

Controls, all accepted:

- the same call with the implicit written: `keepx(B(lo, hi), x := x, h := And(l, h))`;
- the same `And` in checking position at the declaration's result, `{ And(l, h) }`;
- the same shape when the predicate is not a `match` (`fn Box(lo, hi, x) → Type { lo <= x ∧ x <= hi }`);
- binding the pair first: `let b: (B(lo, hi).Has(x)) = And(l, h); keepx(B(lo, hi), b)`.

So the pair is elaborated against the predicate's `match` while `x` is
still a metavariable, and the level the `And` (Σ) node gets from that is not
the one the solved type has. Found writing `Interval::mul_box_has`
(`lib/std/num/float/interval.hthr`), which binds the pair with a typed
`let` as the workaround.

Same family as [[generic-congruence-inferred-type-arg-level-mismatch]]
(an inferred implicit, a `LevelMismatch` only the kernel sees), not shown
to be the same cause.

## Log

- 2026-10-31: 2026-10-31: Root cause: not the match and not the level. The argument's inferred type `And<P, Q>` (`El(app(And#tycode; P, Q))`) met the parameter's `El(app(Iv::Has; I, ?x))` in the unifier's application congruence, which paired the two spines' arguments although their heads were different committed globals, so `?x := Q` (a type code where a `Nat` belongs; the kernel's first complaint about it was the level). The expected type would have solved `?x := x`. A non-match predicate never showed it because `Box(lo, hi, x)` has three arguments and the different-length rule (issues/constrained-predicate-expected-type.md) already refused that pairing. Fix: `U::distinct_heads` in unification.rs; two spines whose heads are different atoms (locals, committed globals, one of each) pair nothing, as two different-length spines already did. Probes in lib/_tests/std/core/logic_tests.hthr, including the no-expected-type case, which now says it cannot infer `x` instead of guessing. `Interval::mul_box_has_in` passes the pair directly.
