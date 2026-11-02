---
title: A case split in a recursion whose ih mentions the split parameter stays the recursion
status: open
labels: [frontend,recursion,elaboration]
area: language
created: 2026-11-02
updated: 2026-11-02
---

A case split inside structural recursion keeps the enclosing guard
([[recursion-guard-takes-nearest-parameter-match]]), except where the
enclosing induction hypothesis's type mentions the split parameter. A theorem
about the parameter is the common case:

```
theorem walk_shape(d: Nat, n: Nat): walk(d, n) = (match n { Zero => 0, Succ(_) => d }) {
    match d { Zero => …, Succ(k) => match n {
        Zero => walk_shape(k, n), Succ(_) => Nat::cong(λ (w: Nat) => Succ(w), walk_shape(k, n)) } }
}
// error: recursive call to `walk_shape` must descend: argument `n` has to be `_`
```

The split on `n` refines the goal in each arm (`walk(Succ(k), Zero) = 0`)
but the ih is a binder of the outer recursion, still at `n`
(`walk(k, n) = match n {…}`), so the call would not fit. Taking the outer
guard here passed the elaborator and only the kernel refused, so
`recursion::guard_param` keeps the split as the recursion when
`Guard::ih_mentions` says so, and the refusal is the old one. Pinned in
`lib/_tests/std/core/recursion_case_split_tests.hthr`.

The fix is to refine the ih along with the goal: revert it into the split's
motive (as `refined_hypotheses` does for an ordinary hypothesis) and hand the
arms a guard whose ih is the reverted binder, instantiated at the arm's
constructor. Today's workaround: split in a helper, or generalize `n` by
passing it varied.

## Acceptance

- `walk_shape` checks.
- A split whose ih would not fit after refinement is refused by the
  elaborator, never only by the kernel.
