---
title: A proof casing an if h: test over a function whose branch uses h is refused by the kernel
status: open
labels: [elaboration,matching,motive]
area: language
created: 2026-11-12
updated: 2026-11-12
---

A function whose `if h: P` branch uses `h` cannot be proved about by casing the same test at a neutral argument since `if h:` became a convoyed match on the bit (PR #586, 2026-11-12):

```heather
fn need(n: Nat, h: 1 <= n) → Nat { n - 1 }
fn f(n: Nat) → Nat { if h: 1 <= n { need(n, h) } else { 0 } }
theorem f_pos(n: Nat, p: 1 <= n): f(n) = n - 1 { if h: 1 <= n { refl } else { false_elim(h(p)) } }
```

> error: the kernel rejected `f_pos`: NotConvertible. no checking site recorded this refusal: the kernel refused `a`, which has type `x = True`, where `decide_bit = True` is expected

`f(n)` unfolds to `Case(λ z'. (leb(1, n) = z') → Nat, leb(1, n), λ a. need(n, decide_true<1 <= n>(a)), …)(refl)`. Motive synthesis abstracts every spelling of `leb(1, n)` (`matching::with_scrutinee`), so the arm binder `a` becomes `z = True`, while `decide_true`'s parameter is `decide_bit<1 <= n>() = True`, a spelling of the bit through the instance that is not abstracted (and cannot be: `decide_true`'s own type fixes it). A `rewrite` with the bit's equation builds the same motive. Over the old `Inl`/`Inr` form `h` was the payload of the generalized decision and the proof went through. The elaborator accepts the motive and only the kernel refuses it, so the message is also poor.

A function whose branches never name `h` has no such term and is proved this way (`larger_is_right` in `lib/_tests/std/core/imperative_statements_tests.hthr`).

## Fix

A convoy-aware motive. Against a goal whose unfolding is a convoyed eliminator `Case(M, s, arms)(refl_s)` stuck on `s`, and a proof that is itself a convoy `match e: s { … }`: abstract only the stuck scrutinee position to `z` and replace the applied `refl_s` by the proof's equation `e: s = z`, leaving `s` as written in `M` and the arms. The motive then mentions `e` (the convoy's motive is `Π(e: s = z). M`, so `plan_convoy` must let `M` see `e`). In the `True` arm the goal is `Case(M, True, arms)(e)`, which reduces to `arm_True(e)`. This is `J`'s transport of the unfolded function along `e`, well-typed for any `z`, and subsumes `with_scrutinee`.

## Done when

`f_pos` above checks as written, with probes beside `before`/`larger` in `imperative_statements_tests` at a neutral argument, for `if h:` and a written `match h:`.
