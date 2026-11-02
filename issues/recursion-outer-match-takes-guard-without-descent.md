---
title: The outermost match on a parameter takes the recursion guard even when no call descends through it
status: open
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
