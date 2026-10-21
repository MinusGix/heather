---
title: IH generalization misses a varying recursive call passed as `j`'s base
status: open
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
