---
title: split/on: structurally named per-constructor goals
status: closed
labels: [frontend,elaboration,syntax]
created: 2026-07-24
updated: 2026-08-05
---

The third `on` head form from docs/sketches/surface-v1.md §2, decided there
but not implemented by [[goal-holes]] (which landed `on ?name` and
`on _: P`). It was tracked inside that issue; this is the standalone home
now that it is closed.

```heather
fn add(m: Nat, n: Nat) -> Nat {
    split m;
    on Zero    := n;
    on Succ(k) := Succ(add(k, n));
}
```

`split m;` replaces the current goal with one named goal per constructor;
`on Ctor(fields) := expr` discharges by constructor name. The sketch's
framing: "this is tactic `cases` with structurally named, order-free goals —
the good version."

## Why it is not just sugar for `match`

The load-bearing caveat, and the reason expression-`match` stays primary
(surface-v1 §2): **`on` arms are leaves**. If computation continues after
the split — a join point — the continuation is the motive, and that is
exactly what expression-`match` already is. `split`/`on` is for when the
split is the last act of the block: common in proofs, occasional in code.

So this is not a second elimination mechanism, it is a *statement-position*
spelling of the one we have, and it should lower to the same `elim_Nat` the
`match` path builds ([[match-recursion]]'s termination analysis and IH =
guarded self-call apply unchanged).

## What it needs from what exists

The pieces are mostly in place after [[goal-holes]]:

- a statement grammar (`Block` with `stmt*`) — landed;
- goals with captured contexts and `on`-discharge — landed; the constructor
  goals are ordinary goals whose captured `Cx` has the arm's binders, which
  is the same capture the `match`-arm case already exercises;
- new: a `split` statement, per-constructor goal *naming* (`Zero`,
  `Succ(k)`, with the binder names coming from the `on` head rather than
  the split), and the requirement that the split's goals are the block's
  result — i.e. the block has no separate result expression once it splits.

That last point is the real design question: today a block is
`stmt* expr on_stmt*` with exactly one result expression. `split` makes the
*goals themselves* the result, so the grammar needs either a distinguished
`split`-terminated block shape or a rule that a block whose last statement
is a `split` takes no result expression.

## When

Not urgent — every proof it would improve is writable as expression-`match`
today. Worth doing when statement-position proofs start reading badly, or
alongside [[surface-proof-automation]]'s `apply`, which raises the same
"statement whose goals are the block's result" question.

## Log

- 2026-08-05: Landed as a **parser desugaring** onto `ExprKind::Match` (managed round; docs/match-equation-split-design.md §5–7). The route this issue proposed — constructor goals in the goal machinery — was rejected on an obstacle it never costed: `goal_base = count_holes(decl)` is a syntactic pre-count, and a split's goal count is an inductive's arity the parser cannot know; plus the binder names come from the `on` head, needing per-goal Cx renaming no other goal performs. The desugaring makes "lowers to the same elimination" byte-identical (asserted by test) and inherits every arm diagnostic. Grammar rule decided: a block whose statement list ends in a `split` takes no result expression; arms and goal discharges share the one `on` loop, told apart by a single token, so arms stay order-free and may interleave with discharges. `split h : e;` is accepted (same node, same field). A split-terminated block *expression* works and does not re-raise [[nested-goal-discharge]] — the caution docs/let-and-blocks-design.md §6 recorded is answered. Known wart, deliberately not fixed: arm diagnostics say `match` where the user wrote `split` (the price of the desugaring; constructor and arm are still named correctly).
- 2026-08-19: Post-I-prime review supplied the compact proof customer and
  confirmed it already checks: `{ split m; on _ := trivial; }` replaces
  `match m { Zero => trivial, Succ(k) => trivial }`. The default arm is the
  useful analogue of applying one closer to every constructor. A general
  all-goals command combinator remains deliberately unowned until a command
  sequence needs more than this existing spelling; [[sequent-binder-expression]]
  owns the adjacent checking-position introduction form.
