---
title: The checker past the second experiment: a loan held across statements, a branch with a join, stored references and the erased owner
status: open
labels: [ownership,library,design]
area: heather-in-heather
milestone: [nh-ownership]
created: 2026-11-25
updated: 2026-11-25
---

What the second experiment ([[ownership-checker-call-and-write-view]], `lib/lang/ownership/call_check.hthr`) did not test of the checker, from its log of 2026-11-25: the rest of package 3 of `docs/language/ownership-design.md` §16 (calls, write views, regions, joins), at the level of the checker and its meaning. Library only, over that module's world-of-callees structure. The bytes level, references stored in memory down to x86, is [[ownership-reference-cells-spike]], which §16 calls the third experiment; this issue does not touch it.

## Scope

- **Stored references and the erased owner** (§15.2, §15.5): a `&mut{o} T` held as a value in a cell, so the run's file holds references; a callee that consumes a collection of them takes an erased in-out owner. `FnSafe`'s frame must then cover what is reachable through stored references, and the meaning's slot is the path it returns to.
- **A branch with a join** (§15.3): two arms whose place states differ (a view dead on one arm, a version bound on the other); the join is the meet, with regions coarsened; residuals under the branch's condition.
- **A loan held across statements**: `let w = &mut x[lo..lo+n]`, writes through `w`, then its death. The second experiment's loan lasts one statement (`CallMut`), so no window is ever `out` between statements and `Sim.on` never needed weakening; this is where "the buffer holds the holder's value outside its out windows, and each out window holds its viewer's value" is first an invariant rather than a step's two premises (`written_back`).
- **A finer returned region**: a signature that places a returned view in a window of its parameter, so the caller may write apart from it. There `FnSafe.view_in` becomes load-bearing for a frame; in the second experiment it is used only to place the view inside the whole object it freezes.

## What it assumes from elsewhere

- **[[ownership-fnsafe-postconditions]]** owns facts about a callee's answer. Assumed here: nothing; a branch on a callee's answer would want it.
- **[[place-check-name-lookup-cost]]** owns the closed verdict's cost. Assumed here: several objects bring back a holder table, which should be a map keyed by buffer.

## Done when

`check_sound` over the extended fragment, one accepted program per addition and a `¬` control for each refusal, and the log answers whether the place states still suffice once references are stored (the condition under which §15's design says a separation algebra might be needed: placement, not the checker).
