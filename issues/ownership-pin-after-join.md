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
