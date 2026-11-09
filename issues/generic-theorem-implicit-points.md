---
title: Let a class-generic theorem take its points implicitly, so a call reads like the carrier's own
status: closed
labels: [elaboration,inference,traits,ergonomics,stdlib]
area: language
milestone: [math-classes]
created: 2026-11-08
updated: 2026-11-08
---

A theorem stated once over a class (`section<K: OrderedField(≈, <, <=, +,
*)>`) cannot be called with its points left to inference. This probe is
refused at the call in `p_use` and at `p_nopoint()`:

```heather
section<K: OrderedField(≈, <, <=, +, *)> {
theorem p_lt_tr({x, y, z: K}, a: x < y, b: y < z): x <= z { StrictOrder::le_of_lt(x, z, linarith(a, b)) }
theorem p_use(a, b, c: K, h1: a < b, h2: b < c): a <= c { p_lt_tr(h1, h2) }
// cannot infer the implicit arguments needed for `OrderedField<K>(≈, <, <=, +, *)`
// in `p_lt_tr` from this call: the expected type or a scoped constraint must pin
// the indices before instance search can run
theorem p_nopoint(): K.unit < K.multiplicative.unit { K.zero_lt_one }
theorem p_use2(a: K): K.unit < K.multiplicative.unit { p_nopoint() }   // same refusal
}
```

`docs/constructive-ordered-field-design.md` ("Calling a generic theorem")
records why: with implicit endpoints the hypothesis `?lt(?x, ?y)` is not
solvable against the carrier's `<` before the carrier is known, so every
generic theorem takes its points explicitly, and
[[constrained-predicate-expected-type]] closed with "implicit endpoints stay
out of scope by design". The expected type does not pin the dictionary either
(`p_use2`).

## What it costs

That one decision shapes most of the ordered-algebra library
(docs/stdlib-math-awkwardness-survey.md §1):

- Every generic call restates endpoints the hypotheses already fix (1,571
  calls to `StrictOrder::`, `PseudoOrder::`, `OrderedAddMonoid::`, …,
  `OrderedField::` theorems in lib/std on 2026-11-08):
  `StrictOrder::le_respects(x, x2, y, y2, hx, hy, h)`,
  `PseudoOrder::le_trans(map(R), A * map(lo) + map(b), A * x + map(b), …)`
  (lib/std/num/float/float_real.hthr), `OrderedAddMonoid::add_respects(…)`.
- A theorem with no point of its own takes a dummy one so a caller's
  carrier pins `A`: `OrderedField::two_pos(x: K)`, `of_nat_nonneg(x: K, n)`,
  `Bisection::quarter(x: K)`, `OrderedAddGroup::neg_zero(x: A)`,
  `lin_one_pos(x: A)`, `RingExpr::of_nat_add(xs: List<A>, …)` (the comments
  in linarith.hthr, ring.hthr and semiring.hthr say so).
- The concrete carriers keep a second copy of the class's theory with
  implicit points and dot syntax, because the generic one is unpleasant to
  call: 65 `CReal::` and 68 `Rat::` theorem names coincide with a generic
  class theorem's (`add_le_mono`, `le_of_same_l`, `mul_pos`, `neg_lt`, …),
  most re-proved rather than read off the instance. `mono` then lists the
  carrier copies as well as the class laws (lib/std/tactic/mono.hthr).

## Direction

Inside a section the indices are not unknown: the section's dictionary is in
scope, and `h1: a < b` has the section's own `<` as its head. Two routes,
not exclusive:

1. **Retry the index rungs after the explicit arguments.** When a call's
   class indices are still open after its arguments are unified, fill them
   from the scoped dictionary (rung 1) or the carrier's designations (rung 2)
   and run instance search then, instead of refusing at the first attempt.
2. **Solve `?lt(?x, ?y) ≟ lt(a, b)` first-order when the head is a local
   or a dictionary field**, as a ranked approximation in the sense of
   [[unifier-guesses-postponed]] (P2 of docs/elaborator-principles-survey.md):
   it is the only solution that keeps `?lt` an index of the class.

The cause above is the design note's statement; this issue has not
re-traced it in `apply_implicit`, and the first step of a round is to do
that.

## Acceptance

- `p_use` and `p_use2` above check, inside a section and at `Rat`/`CReal`
  (a call `StrictOrder::le_of_lt(h)` at `Rat`).
- A negative control: a call whose hypotheses mention two carriers' orders
  still refuses, naming the parameter.
- One generic file (`ordered_field.hthr` or `ordered_sign.hthr`) moves to
  implicit points, and the dummy points listed above are deleted.

## What it assumes from elsewhere

- **[[method-call-on-constrained-carrier]]** owns `x.le_trans(h1, h2)` at a
  constrained receiver. Assumed here: nothing; the two compose (the dot call
  supplies the first point, this issue the rest).
- **[[type-owned-namespaces]]** owns whether `CReal`'s copies can become
  reachability through the instance. Assumed here: only that removing the
  copies needs generic theorems that are as easy to call.

## Log

- 2026-11-08: Re-traced in `apply_implicit`. The design note's cause was not
  the one: the hypotheses' reads already solve the points and the indices
  (`?< := <` by the postponed guess, or from the section's dictionary), and
  what stayed open was the **carrier** `?K`, which only the slots' own types
  mention (`?x : El ?K`, `?< : El ?K → El ?K → Type`). No read ever looked
  at a solution's type, so the class goal never became meta-free and the
  call was refused before search. `Elaborator::learn_from_solution_types`
  (crates/elab/src/solution_check.rs), run by `retry_obligations` ahead of
  the solver obligations, reads each solved slot's kernel type against its
  declared type while that type is open. Route 1 then works as the ladder
  already did: scope rung inside a section, designation at `Rat`/`CReal`.
  Neither route of the Direction needed building.
- A slot written while its type was open is judged when the type closes and
  undone if it does not fit, so the negative control (hypotheses at `Rat` and
  `CReal`) refuses with "could not infer the implicit argument `z`", as the
  same call at a concrete carrier does.
- The issue's probes are lib/_tests/std/algebra/ordered_field_tests.hthr's
  `implicit_*`/`no_point*`. The dummy points are gone (`two_pos`,
  `of_nat_nonneg`, `of_nat_pos`, `of_nat_lt_succ`, `Bisection::quarter`,
  `neg_zero`, `one_apart_zero`, `Ring::inv_unit`, `lin_one_pos`,
  `lin_num_pos`, `lin_num_nonneg`, `lin_zero_le`); `RingExpr::of_nat_*` keep
  their atom list, which `ring`'s reflection builds positionally.
- Moving `ordered_field.hthr` itself to implicit points (the third acceptance
  bullet) is ~700 call rewrites plus `mono`'s positional lemma table, and is
  filed as [[class-theorems-implicit-points]]. Closed.
- 2026-11-09: merged over class-carrier numerals (#494). A point-free
  theorem stated only in numerals (`two_pos(): 0 < 2`) does not name its
  section's carrier, and the section check refuses it (sections-design
  §4.1), so it is written `K.unit < 2`.
