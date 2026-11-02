---
title: grind: a caller's tactic for premises nothing else proves (grind_by)
status: open
labels: [tactics,metaprogramming]
area: tactics
milestone: [tac-general]
created: 2026-11-02
updated: 2026-11-02
---

[[grind-lemma-premises]] proves a premise by the graph, a local or a hint that
is no equation (`Defeq`), or `Synth` (docs/grind-design.md §11). Wanted: a
caller's tactic as the last resort, `grind_by(names, hints, t)`, run at the
premise's statement with the goal's locals (`focus`), its result checked
against the premise before it counts, so that a premise needing a derived
step (`apply(Nat::le_trans(…), assumption())`, `norm_num()`, later `omega`)
does not need its proof written as a hint.

A prototype (in the round's history, not shipped) did this with `attempt`
and `focus`. It passes a probe whose premise `apply` closes, but on
`commit_chain`'s first branch (lib/std/parser/parser_diagnostics.hthr) with
`t = apply(Nat::le_trans, assumption())` (no arguments, so `apply` leaves
`le_trans`'s middle point a hole) it changed which instances were added:
`commit_later`'s instance at `Lt(a, b)` was no longer added although the
local `first: a.Lt(b)` is tried before the tactic, and two
`commit_not_later` instances were added instead. With `assumption()` as `t`,
or `apply` given every argument, the instances are the expected ones.

First step: find what the hole-leaving `apply` run changes (a hole solved
by a successful run that a later `Defeq` reads, or a proof with a hole left
in it that the `infer`+`Defeq` check passes and that then merges two
classes), and reject a premise proof that still has holes. Done when
`grind_by` closes `commit_chain`'s branches with one tactic and no hint.
