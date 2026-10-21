---
title: Eliminate a local variable along an equation (`subst`)
status: closed
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

## Log

- 2026-10-21: Done: `subst(h, e)` (crates/elab/src/subst_local.rs, docs/equation-rewrite-design.md §8). Reverts every later local depending on x (transitively, through h too) into a Π-telescope motive, keeps x in Γ as an alias of t (so no local is reordered and t may mention later locals), eliminates h as J's q when h : t = x (reverted when h : x = t and something mentions it, since sym(sym h) is not h). Tests: crates/elab/tests/subst_local.rs.
