---
title: The outermost match on a parameter takes the recursion guard even when no call descends through it
status: closed
labels: [frontend,recursion,elaboration]
area: language
created: 2026-11-02
updated: 2026-11-02
---

The mirror of [[recursion-guard-takes-nearest-parameter-match]]: the
*outermost* `match` on a parameter takes the guard even when no self-call
descends through it, so a recursion on an inner parameter is refused:

```
fn inner(d: Nat, n: Nat) → Nat {
    match d { Zero => 0, Succ(k) => match n {
        Zero => d, Succ(m) => inner(d, m) } }
}
// error: recursive call to `inner` must descend: argument `d` has to be `k`
```

Here `n` descends (`m`) and `d` is passed unchanged, so the recursion is on
`n`, and the `match d` around it is a case split. A nested case split no
longer takes the guard (`recursion::guard_param`, `descends_through`), but
the outermost `match` on a parameter still does unconditionally: with no
guard in scope there is nothing to fall back to, and the existing refusal
for `f(n)` under `match n` ("has to be `k`") relies on it. The planner
(`recursion::plan`) already treats the outer `match` as not recursive.

Making the outer `match` a case split also has to keep ih generalization
from planning at it (`varying_params` at `d` sees nothing varied today, but
a split under it that varies `d` would), and keep the refusal wording for a
lone `match` whose calls descend nowhere.

## Acceptance

- `inner` checks, and `inner(2, 5) = 2` by `refl`.
- `fn f(n: Nat) → Nat { match n { Zero => 0, Succ(k) => f(n) } }` is still
  refused naming `k`.

## Resolution (2026-11-02)

`recursion::guard_param` with no guard in scope now asks
`outer_case_split`: the `match` is a split when no self-call descends
through it (`descends_through`) and one does through a `match` on another
parameter inside its arms (by name, skipping a name the arm rebinds). Then
the inner `match` takes the guard, and ih generalization plans there. A lone
`match` with nothing inside to be the recursion keeps the guard, so
`lone(n)` under `match n` is still refused naming `k`. The planner reads the
top `match` the same way. `descends_through` now counts a nested `match`'s
binders as the arm's only when its scrutinee reads the arm's names (a
predecessor's predecessor), not when it is on another parameter.

`inner` checks (`inner(2, 5) = 2` by `refl`), and a theorem by the inner
recursion under the split too. Making the outer `match` a split exposed a
wrong-meaning shape where calls vary the split's parameter, which the
computed and `if` spellings already had on master: fixed and recorded as
[[recursion-branch-on-varied-parameter]]. Probes:
`lib/_tests/std/core/recursion_case_split_tests.hthr`.
