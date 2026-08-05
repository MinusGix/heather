---
title: let-else: the one-non-absurd-branch match, with its equation
status: open
labels: [frontend,syntax,elaboration,design]
created: 2026-08-05
updated: 2026-08-05
---

From [[match-with-equation]]'s design space, deferred out of its landing round (2026-08-05). Most equation-binding consumers scrutinize a `Res` under a hypothesis that makes every arm but one absurd; the sugar is
`let Out(ws) with h := e else b => absurd(…)` — one non-absurd branch, equation included.

Now cheaper than when sketched: it is a degenerate `match h : e { … }` and desugars the same way `split` does (parser-level, onto `ExprKind::Match`; docs/match-equation-split-design.md §6 is the pattern to copy). Not scheduled; the trigger is a second real consumer reading badly, same bar the equation binding itself was held to.

The other reusable answer for the same pattern is an inversion record per shape ([[surface-existential]]'s `BindInv` move), which needs no syntax; this sugar is for the shape whose inversion lemma has one consumer.
