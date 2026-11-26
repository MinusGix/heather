---
title: A source that continues after an `if` does not pin against the checker's branch by conversion
status: open
labels: [ownership,library,design]
area: heather-in-heather
milestone: [nh-ownership]
created: 2026-11-25
updated: 2026-11-25
---

From [[ownership-site-facts-into-the-checker]]. The checker's meaning carries what follows a branch into each arm (`mean_then`): a branch is `convoy(test, arm a then the rest, arm b then the rest)`, the convoy a source's `if h:` elaborates to when the `if` ends the function. So a function whose `if` is in tail position pins by `refl` (`poke_reflects`, `hop_le_reflects`), but a source that continues after the `if` (`let a = if h: … { … } else { … }; rest`) elaborates to `rest` over a convoy of values, and its pin against the checker's body is not a conversion. The fifth experiment wrote each arm as a whole body for the same reason.

## Wanted

Decide the correspondence a generator needs: reflect `let a = if …; rest` by moving `rest` into the arms (the checker's shape, at the cost of the body's size), or give the meaning a join that matches the source's convoy of values (a phi), with a pin lemma for it, measured.

## Done when

A function with code after an `if` has its pin by conversion or by one stated lemma per function, and its safety from `check_owned`.

## Log

- 2026-11-25: Decided (docs/language/ownership-design.md §20.3): the join binds its outputs. A branch names its outputs and after it each is `convoy(test, the yes arm's value, the no arm's value)`, the term the source's own `let x = if h: … else …; rest` elaborates to; nothing after the join is carried into the arms. The carried form also reads what follows `k` branches in sequence `2^k` times, in the meaning and in what the function owes. Not built on `call_check.hthr`: a requirement on the checker built over the fixed interfaces (§20.6), closed by it. The sixth experiment ([[ownership-coded-values]]) is asked for one pin of a function that continues after its `if` in this form.
- 2026-11-25: The interface this is built against is fixed in docs/language/ownership-design.md §21 (the build's probes: §21.5).
