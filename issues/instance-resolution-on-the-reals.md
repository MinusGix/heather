---
title: Instance resolution is 18% of a cold check of the reals
status: open
labels: [performance,elab,typeclass]
area: language
created: 2026-11-11
updated: 2026-11-11
---

Instance resolution is 18% of a cold check of the reals, six times its share elsewhere. Found while writing [[performance-overview-2026-11-11]].

`heather check lib/std/analysis/closed_interval.hthr` cold at width one, release binary, 2026-11-11: 88.2 s over 29 modules and 2,025 declarations, of which `resolve_ns` (the phase of `Elaborator::resolve_goal_from`) is 15.6 s. On the showcase the same column is 0.37 s of 13.5 s (3%), and over the whole library it is 35 s of 786 s (4.5%), so nearly half of the library's resolution time is in this one closure.

The closure is `creal`, `sequence`, `supremum`, `real_fn`, `closed_interval` and what they import: goals over `OrderedField` and the classes below it, where each goal can be reached through several parents of the tower ([[ordered-algebra-api]]).

Not yet known: how many goals there are against how long each takes (the `resolve_goals` counter beside the column says), whether the time is failed candidates tried before the right one, and whether the open-derivation memo is being missed because goals differ only by context prefix. [[instance-match-walks-the-template-twice]] is a known cost on the same path.

## Done when

The cause is named from a `--timings` table and a profile of one heavy declaration (`supremum::OrderComplete::below_located`, 11 s), and resolution is back near its 3 to 5% share on this closure.
