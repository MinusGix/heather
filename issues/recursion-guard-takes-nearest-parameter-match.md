---
title: Structural recursion takes the nearest match on a parameter as its guard
status: closed
labels: [frontend,recursion,elaboration]
area: language
created: 2026-10-29
updated: 2026-11-02
---

The structural recursion check takes the nearest enclosing `match` on a
parameter as the recursion's match, so a self-call under an inner case
split on *another* parameter is refused as not descending:

```
fn walk(d: Nat, n: Nat) → Nat {
    match d { Zero => 0, Succ(k) => match n {
        Zero => walk(k, n), Succ(_) => Succ(walk(k, n)) } }
}
// error: recursive call to `walk` must descend: argument `n` has to be `_`,
//        the predecessor bound by the enclosing `match`
```

`d` descends (`k` is its predecessor) and `n` is passed unchanged. Writing
the inner split on a non-variable (`match Nat::add(n, 0)`) or in a helper
is accepted. Probe on master 4f0ac27 ([[proof-patterns-audit-2026-10]]).
Memory has a neighbouring note from the measure-loops round (2026-10-26):
"a theorem whose recursion is inside a nested `match` under λ/let says
'applied to too many arguments' — put the match at the top".

[[fn-recursion-means-the-function]] owns spellings that are refused because
their compiled meaning would differ; this one would compile to the same
recursor on `d`, so it is a guard-selection gap, not a meaning gap.

## Acceptance

- `walk` checks, and `walk(24, 3) = 24` by `refl`.
- A self-call that descends neither match is still refused, naming the
  matches it tried.

## Resolution (2026-11-02)

Still refused on master ff5be99 (the let-staleness fix did not touch guard
selection). `recursion::guard_param` now picks the guard at every `match`
route: inside the recursion, a `match` on a parameter is the recursion only
if a self-call in its arms passes, at that parameter, something built from a
name the arm binds (`descends_through`); otherwise it is a case split and the
enclosing guard stands, as under `match Nat::add(n, 0)`. Ih generalization
(`lib.rs`), the deep-pattern check (`patterns.rs`) and the planner
(`recursion::plan`) read the same choice. Every call a guard on a split could
accept passes such a name, so the change only turns refusals into
acceptances. Accumulator splits (`go(k, 1)` under `match acc`) check too, with
the accumulator generalized at the outer recursion.

A call that descends through neither is refused at the outer guard, and the
refusal names the split: "The `match` on `n` inside it is not the recursion:
every recursive call in its arms passes it along unchanged…" (`Cx::case_splits`).
Probes: `lib/_tests/std/core/recursion_case_split_tests.hthr`.

Residue, each with an owner:
- a split whose enclosing ih mentions the split parameter (a theorem about
  it) stays the recursion, refused as before:
  [[recursion-case-split-dependent-ih]];
- the outermost `match` on a parameter still takes the guard when no call
  descends through it: [[recursion-outer-match-takes-guard-without-descent]].
