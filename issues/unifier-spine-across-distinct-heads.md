---
title: Implicit inference takes the arguments of an application with a different head
status: closed
labels: [elab,unifier,diagnostics]
area: language
created: 2026-10-30
updated: 2026-11-03
---

Found while building omega's guard round ([[omega-reads-bool-guards]]).
An implicit solved against an application with a *different* global head
takes the other head's arguments, whatever their type:

```heather
fn g(n, m: Nat) → Bool { n.leb(m) && !m.leb(n) }
theorem pick({a, b: Bool}, h: (a && b).IsTrue()): a.IsTrue() { a.is_true_and(b, h).left }
theorem t(n, m: Nat, h: g(n, m).IsTrue()): n.leb(m).IsTrue() { pick(h) }
// error: this has type `IsTrue(g(n, m))`, but `IsTrue(and(n, m))` is expected here
```

`Bool::and(?a, ?b)` against `g(n, m)` solved `?a := n`, `?b := m`: two
`Nat`s for two `Bool` metas. The refusal is the elaborator's, so nothing
unsound reaches the kernel, but the message names a type nobody wrote, and a
solution that should not exist was committed. Two readings of the right
answer, which the round should choose between:

- rigid–rigid at distinct global heads learns nothing (and the refusal says
  `IsTrue(g(n, m))` against `IsTrue(?a && ?b)`), or
- one side is unfolded first, as conversion would (`g` is a `fn`, its body
  `n.leb(m) && !m.leb(n)`), so `pick(h)` elaborates.

omega no longer depends on either: §17 of
`docs/tactics/omega-measure-reduction-design.md` binds the unfolded guard as an
alias instead. Acceptance: the probe above is refused naming `g(n, m)`
against `?a && ?b`, or accepted; never a solution of the wrong type.

## Log

- 2026-11-02: [[unifier-lazy-delta]] proposes the second reading (unfold at the head mismatch) as the general rule.
- 2026-11-03: Fixed by the second reading ([[unifier-lazy-delta]]): `Bool::and(?a, ?b)` against `g(n, m)` unfolds `g` to `n.leb(m) && !m.leb(n)`, so `pick(h)` elaborates. The probe is lib/_tests/std/core/bool_tests.hthr `lazy_delta_pick_through_g`.
