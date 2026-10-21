---
title: Eliminate a local variable along an equation (`subst`)
status: open
labels: [frontend,elaboration,proofs,ergonomics]
area: tactics
milestone: [tac-general]
created: 2026-10-21
updated: 2026-10-21
---

`rewrite(h, e)` refuses when abstracting the left side leaves a motive that
is not a type — something else in the goal (or a hypothesis it mentions)
depends on that exact term (`docs/equation-rewrite-design.md` §2, the
`v : P(n)` test). When `h : x = t` (or `t = x`) and `x` is a **local
variable**, Lean's `subst` always succeeds: it generalises every hypothesis
whose type mentions `x`, eliminates with `J` at a motive over all of them,
and leaves the goal with `t` for `x` everywhere.

Wanted: `subst(h, e)` at a checking position, `e` checked in a context where
`x` is replaced by `t` in every later binder's type. The dependent-telescope
generalisation is the work; the `match` convoy (`elab_convoy`) and
`generalize_index` (`indexed.rs` §6.1) are the nearest existing pieces.
