---
title: IH generalization misses a varying recursive call passed as `j`'s base
status: closed
labels: [frontend,elaboration,recursion,motives]
area: language
created: 2026-10-21
updated: 2026-10-21
---

A recursive call that varies a non-decreasing parameter is refused when it is
an argument of `j` (the transport's base), and accepted when the same call is
hoisted into a `let` in the same arm (master `4bbbc06`):

```heather
import logic;
import nat;
fn Le(a: Nat, b: Nat) → Type { match a { Zero => True, Succ(k) => match b { Zero => False, Succ(m) => Le(k, m) } } }
theorem f(a: Nat, b: Nat, e: a = b): Le(a, b) {
    match a {
        Zero => trivial,
        Succ(k) => j(e, λ y q => Le(Succ(k), y), f(k, k, refl)),
    }
}
```

```text
error: recursive call to `f` must pass `b` unchanged: … only when the `match`
is checked against a known result type and the varying call is visible in its
arms (docs/ih-generalization-design.md); here it was not
```

Writing the arm as `{ let ih: Le(k, k) = f(k, k, refl); j(e, λ y q => Le(Succ(k), y), ih) }`
checks. So the call *is* in the arm; the scan that decides generalization does
not see it in that position. Every congruence proof over a relation read off
one side (`ITree::same_sym`, `same_bind` in `lib/std/itree.hthr`) has this
shape: rewrite the other side with `j`, then recurse.

## Done when

The `j`-argument form checks like the `let` form, or the diagnostic says
where the call must move.

## Log

- 2026-10-21: Fixed. The scan was right and the walk under it was not: `surface::for_each_child`, the one walk every recursion scan uses (`recurses_on`, `varying_params`, `cov_depth`), fell through `_ => {}` on `j`, a record update and a `let code` statement, so a self-call there was invisible to the planning and met the by-binder refusal when elaborated. The walk is now exhaustive over `ExprKind` (a new surface form without a line there is a compile error) and also enters a written `match` motive. Tests in `crates/elab/tests/ih_generalization.rs`: the issue's shape, a program computing through `j` at a literal, a call inside `with { … }`, and a negative control (a wrong varied argument under `j` is still refused by the ih's domain). Types (`TyLit`, annotations) are still not entered: a self-call written inside type syntax is not scanned.
