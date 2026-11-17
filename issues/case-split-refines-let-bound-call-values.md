---
title: A case split on a value the callee let-binds refines the hypothesis that reads it
status: open
thread: Refine hypotheses through calls in case splits
labels: [elaborator,matching,proofs]
area: language
milestone: [lang-proof-modularity]
created: 2026-11-16
updated: 2026-11-16
---

`Stmt::pair_known`'s `Dataflow` arm binds `let known =
body.nodes.leaves_known()`, computes `before` from it, and tests a
condition on `before` whose `True` arm is `known`. `Region::paired` takes
`carried: Compute(Dataflow(body)).pair_known(rest, homes, out) = Cons(f,
fs)` and needs a split on `leaves_known()` to see `carried` at `Nil` (to
refute it) and at `Cons(g1, gs)`.

Since goal-motive-synthesis-design §4.7, `match rest.reads_known()`
refines `carried` (the reduced left side is stuck on that test). A split
on `body.nodes.leaves_known()` does not: after reduction the call occurs
only inside other calls' arguments and in a branch, which are no stuck
positions, and the reduced type no longer spells it as written. So the
proof keeps the inner written motive `as λ l => body.nodes.leaves_known() =
l → (match …(l) { False => Nil, True => l }) = Cons(f, fs) → …` applied to
`(refl, carried)`.

## Wanted

A split on a call refines an equation whose reduced side mentions the call
where the callee let-bound it, at every such position at once (the goal's
§4.3 syntactic reading of the exposed type is the nearest rule; it did not
find the call in the whnf of `carried`, whose condition the reduction had
already rewritten).

## Done when

`Region::paired` is written with motive-free matches.
