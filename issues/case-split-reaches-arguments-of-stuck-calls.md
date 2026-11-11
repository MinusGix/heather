---
title: A case split on a definition's test does not reach a call that is an argument of another stuck call
status: open
labels: [tactics,proofs,ergonomics]
area: tactics
milestone: [tac-general]
created: 2026-11-11
updated: 2026-11-11
---

`match h: test` in a proof specialises the positions its goal is *stuck*
on (`docs/goal-motive-synthesis-design.md` §4.5). A call whose value is
only an argument of another stuck term is not such a position:

```
fn pick(n: Nat, a, b: Nat) → Nat { match n.leb(3) { True => a, False => b } }

theorem pick_arg(n, a, k: Nat): k.leb(pick(n, a, a)) = True → k.leb(a) = True {
    match h: n.leb(3) { True => λ p => p, False => λ p => p }   // refused
}
```

`k.leb(…)` waits on `k`, so reduction never asks for `pick(n, a, a)` and
its test is not collected. Met three times writing
`lib/std/text/regex/regex_table.hthr` (`x <= Regex::rep(bs, c)`,
`Mem(Regex::rep(bs, c), …)`, `T.Label(T.next(s, c), w)`); each is stated at
a name instead (`rep_max_at`, `rep_mem_at`, and `step_label` over the row
found), with a one-line corollary at the call.

## What would fix it

Collect candidates from the arguments of neutral terms as well: after a
position is found stuck, reduce its spine's arguments and look again, to
the rung's budget. The abstraction must then happen in the goal with those
arguments reduced, which is a deeper normal form than the rung builds
today, so the cost on large goals wants a look before it is on by default.

## Done when

`pick_arg` in `lib/_tests/std/core/match_motive_below_tests.hthr` checks
without its `expect-error`, and `rep_max_at` / `rep_mem_at` are folded
into `rep_max` / `rep_mem`.
