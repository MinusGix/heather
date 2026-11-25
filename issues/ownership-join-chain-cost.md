---
title: A chain of joins, each reading the last one's output, is quadratic to pin: the source's own let chain is the same term
status: open
labels: [ownership,kernel,elaborator]
area: heather-in-heather
milestone: [nh-ownership]
created: 2026-11-25
updated: 2026-11-25
---

From [[ownership-coded-values]] (its measurements, `lib/_tests/lang/ownership/coded_tests.hthr`). A join that binds its outputs (`docs/language/ownership-design.md` §20.3) is linear where the joins are independent, and a function that continues after its `if` pins by `refl`. One shape is not linear: a chain in which each join's test and arm read the previous join's output. Each output is `convoy(test, yes's, no's)`, the next join mentions it in its test and in an arm, so the term is substituted at each use and shared only where the kernel sees the same closure; the pin and the discharge are quadratic in the chain's length and ran out of fuel by 64 joins.

This is not the checker's: the source's own `let a = if h: … ; let b = if h2(a): … a … ;` chain elaborates to the same term (an elaborated `let` is its value), so a source function of that shape costs the same to check with no reflection at all.

## Wanted

Decide where the sharing is kept: a `let` the kernel keeps as a binding through conversion (so the two sides share the bound value by name), or a joined value the reflector abstracts behind a lemma per join where the chain is long. Measure the source function alone first, at doubling lengths, to state what the elaborated `let` chain costs before anything is reflected.

## Done when

The chain's pin and discharge are linear at doubling lengths, or the cost is shown to be the source's own with its issue in the elaborator's or the kernel's thread.
