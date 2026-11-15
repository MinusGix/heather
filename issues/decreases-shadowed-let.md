---
title: A let that shadows a decreases function's parameter breaks its obligations and unfolding
status: closed
labels: [elaboration, termination]
area: language
code: crates/elab/src/measure.rs:172
created: 2026-11-02
updated: 2026-11-02
---

In a `decreases` function, a block `let` that rebinds a name the measure
mentions, or any binder an obligation needs, goes wrong in two ways:

1. **The obligation compares the new value with itself.** In
   `match h: decide_bit<1 <= m>() { True => { let m = m - 1; f(m, …) }, … }`
   with `decreases m`, the call's obligation is shown as `m < m` and
   `omega` refuses it. The measure's `m` means the parameter, but the
   lifter reads it as the latest binding, which is the alias, and the alias
   substitution then rewrites both sides (`lift_obligation`, measure.rs).
2. **The unfolding companions decline.** `select_scope` returns `None` when
   a binder the obligation needs is shadowed later, so the site is not
   lifted. `f#ext` then cites an `f#obl_N` that does not exist ("the
   generated `f#ext` was refused (unbound name `f#obl_1`)"), and `f_unfold`
   is missing. A function with `let m = m__in; …; let m = m - 1;` before
   the condition's match shows this.

The probe `shadowed` in `lib/_tests/std/core/decreases_unfolding_tests.hthr`
pins case 1.

**Workaround in use.** The `while` lowering puts its body in SSA form
(`crates/elab/src/alpha.rs`, `ssa`) before handing it to `decreases`, so
none of its `let`s shadow (docs/language/sequencing-surface-design.md §16).

**Fix direction.** Alpha-rename shadowing block binders before the walk,
with the same uniform renamer, so the measure and every lifted telescope
name each binder once. That would also let `select_scope` stop declining
shadowed binders.

## Log

- 2026-11-02: Found while building `while` loops. In the same round,
  `select_scope` learned to include an equation binder about a needed
  binder, so an argument passed through a non-shadowing `let` keeps the
  arm's equation (`alias_before`, `alias_inside` in the same probe file).
- 2026-11-02: Fixed. `alpha::deshadow` renames every binder that shadows a
  name in scope (a parameter, or an enclosing or earlier binder: block
  `let`s, `let { … }` patterns, arm binders, equation binders, λ binders)
  to a fresh `name__N` across its scope, and `elab_measure_decl` /
  `elab_measure_group` lower the deshadowed declaration
  (`measure::deshadowed`). So the measure and every lifted telescope name
  each binder once, and `select_scope`'s shadow checks no longer fire on a
  `decreases` body. The probes `shadowed`, `rebound` (case 2: needed binder
  shadowed later, `rebound_unfold` exists), `shadowed_arm` and the
  negative control `shadowed_grows` (refused as `m__1 < m`) are in
  `lib/_tests/std/core/decreases_unfolding_tests.hthr`. The `while`
  lowering's SSA pass stays: its condition is placed after the hoisted
  `let`s and must read the parameters.
- 2026-11-02: [[recursion-on-elaborated-terms]] proposes running the structural recursion planner over the same `alpha::deshadow` (docs/elaborator/elaborator-principles-survey.md §6).
