---
title: Tactics see a block's let facts as the goal's locals
status: closed
labels: [tactics,host]
area: tactics
created: 2026-10-27
updated: 2026-10-27
---

A fact bound by a block `let` was invisible to every tactic that searches the
goal's hypotheses. In `Series::decay` (`lib/std/num/float/series.hthr`, on
the monotonicity branch of [[monotonicity-tactic]]),

```heather
let step: (e <= s.term(m).abs()) = …;
… := by mono()
```

`mono()` did not find `step` and had to be handed it as `mono_with([step])`;
`assumption()` and any other Heather tactic that walks `goal().locals` missed
it the same way. Parameters, `λ` binders and match fields were seen.

## Root cause

A block `let` is not a kernel binder. The elaborator keeps it as an alias
(`context::Alias`, `Cx::aliases`) and inlines its value at every use, so Γ
never grows. The host's `Goal` answer (`Elaborator::goal_view` in
`crates/elab/src/host.rs`) listed exactly `cx.gamma`'s entries, so an alias
had no `LocalRef` and no statement a tactic could see. Nothing substituted the
`let` away from the tactic deliberately; the view simply never read
`cx.aliases`.

## Fix

The run issues each visible `let` as a local of the goal, between the binders
it was bound among (most recent first, as `Goal` already ordered binders): a
handle to its value and one to its statement, scoped at the goal. A `let` is
visible when its name still means it (no later binder or `let` of that name)
and it was written (not a `#` name of the elaborator's), the same rule the
speller uses for an alias's name. `Local(ref)` of a `let` reifies to its value,
as a use of the name in source would, so it stays transparent to conversion;
`Lam` refuses to abstract one (it is no binder). A `let` the returned `Expr`
names outright is recorded as spliced, since its value is then in the proof
the kernel checks; one reached only through a handle stays unspliced and its
block hands its value to the kernel as before
([[unused-let-value-unchecked]]).

## Log

- 2026-10-27: Fixed as described above (design: docs/metaprogramming/host-elaboration-interface-design.md §17). Probes in lib/_tests/std/tactic/tactic_tests.hthr; all four positives fail before the fix. On the monotonicity branch, `by mono()` replaces `mono_with([step])` in `Series::decay` and `mono_with([eb])` in `Interval::widen_has`. Projections of a local (`kq.left`) are still not hypotheses of their own.
