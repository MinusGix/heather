---
title: an `on ?decN` block with a `let` leaves a `decreases` fn without `f_unfold`
status: closed
labels: [elaborator, recursion]
area: language
created: 2026-11-16
updated: 2026-11-16
---

A `decreases` function whose `on` clause is a block that binds a `let`
checks, but its unfolding companions are not built: it gets no `f::True`
branch equations and no `f::induct`, and `induct f(…)` answers "`f` is not a
recursive function whose body is a tree of tests". The same discharge
written as a call of a lemma builds everything.

```text
fn halves(x, acc: Nat) → Nat decreases x {
    if h: 0 < x { halves(x.half(), acc + 1) } else { acc }
    on ?dec1 := { let d = x.half_add_le(); omega };   // no halves::True, no halves::induct
}
// on ?dec1 := { half_below(x, h) };                  // builds both
```

`built` is false in `declarations.rs` (the `f_unfold` parts loop): one of the
generated parts is refused, and the reason is kept in `unfold_refusals`
under `f_unfold`, not shown where the missing equation is asked for.

Two things to do: build the parts when the discharge binds a `let` (the
lifted obligation, `f#obl_N`, presumably loses the `let`'s scope or its
type), and have `f::True`/`induct f` report the recorded refusal instead of
"not a recursive function".

Probe to add when fixed: `lib/_tests/std/tactic/induct_tests.hthr`, `halves`
with the `let` form of its `on` clause.

## Resolution

The lifted `f#obl_N` quantifies the binders its goal and the writer's `on`
name (`measure::select_scope`). `omega` names none, so `h: 0 < x` was left
out of `halves#obl_1`, its `omega` got stuck, and the declaration fell back
to the un-lifted lowering with the companions declined. Where the `on`'s
expression holds a search that reads its context (`omega`, `linarith`,
`known`, … — `defaults::is_context_search`), the arithmetic facts in scope
about the goal are now chosen too (`Rewrite::with_read_facts`), as a found
proof's are. Where `f_unfold` is still not built, the reason is recorded
under `f::induct` and the branch equations' names, so `induct f(…)` and
`f::True` report it. Probe: `halves_let` in
`lib/_tests/std/tactic/induct_tests.hthr`.
