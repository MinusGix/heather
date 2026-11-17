---
title: A case split in a recursion whose ih mentions the split parameter stays the recursion
status: open
labels: [frontend,recursion,elaboration]
area: language
created: 2026-11-02
updated: 2026-11-17
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

## Log

- 2026-11-02: A top-level recursion lowering would retire this family: [[recursion-on-elaborated-terms]]; meanwhile [[recursion-meaning-check]] catches miscompiles.
- 2026-11-04: 2026-11-04: Recursion at the top ([[recursion-below-nat-fallback]]) generalizes `n`, but `walk_shape` still does not check there: the call passes the arm's `n`, which a `match` does not substitute by the arm's constructor, so its type is about `n` while the goal is about `Zero` in any lowering. The remaining fix is a match refinement (the arm's `n` is the pattern), not a recursion one (docs/language/recursion/recursion-at-the-top-design.md §5). Passing the constructor (`walk_shape(k, 0)`) is accepted already.
- 2026-11-17: 2026-11-17: `walk_shape` checks: the call's result, stated at `n`, is carried along the split's equation to the arm's goal (docs/language/matching/arm-readings-design.md §5, `Readings::coerce`), which is the match refinement the 2026-11-04 entry asked for. The probe in recursion_case_split_tests is now positive. The second acceptance line (a split whose ih would not fit is refused by the elaborator, never only by the kernel) is not examined.
