---
title: Check each structural recursion's unfolding equation, so a miscompile is a refusal
status: open
labels: [recursion,elaboration,soundness-of-meaning]
area: language
created: 2026-11-02
updated: 2026-11-06
---

Structural recursion is compiled at a surface `match`, and when the planner
(`recursion::plan`) misses a form, the result is a well-typed term that means
a different function. The kernel accepts it and `refl` proves the wrong
equation: [[recursion-let-reads-changing-parameter]] (`u(1, x) = x + 1` where
the source says `x + 11`), [[recursive-arm-reads-outer-scrutinee]], and the
branch-on-varied-parameter bug of PR #389 (`v2(1, [3, 0, 4])` compiled to 7,
the source says 0). This is the only class of elaborator bug the kernel
cannot catch (docs/elaborator/elaborator-principles-survey.md §6).

## Proposal (P4 of the survey)

For every structurally recursive definition, generate its unfolding equation
per constructor of the decreasing parameter,
`f(C(ȳ), x̄) = body[f][n := C(ȳ)]`, and have the kernel check it by
conversion at declaration. A correct compilation should convert (both sides
reach the same arm, with self-calls as `F(k, …)`); each of the three bugs
above differs at an open argument and is refused, located at the definition.
The `decreases` lowering already generates `f_unfold` with a proof
(docs/language/recursion/decreases-unfolding-design.md); structural recursion needs only
conversion.

## Plan

1. A reporting mode over the whole library (a `heather check` flag or a gate
   option) that lists definitions whose equation does not convert. Read the
   list: each entry is either a miscompile (file it) or a false refusal
   (convoy, course-of-values window, dependent ih) to fix or exempt.
2. Turn it into a refusal once the list is empty or every entry has an
   issue. Optionally keep the equations as citable `f_unfold_<Ctor>`
   theorems, as interface definitions already do.

## Acceptance

- The probes from [[recursion-let-reads-changing-parameter]] and #389's
  `v2`, with the planner's refusal disabled, are refused by the meaning
  check, not accepted.
- The library passes in refusal mode.
- Costs stated as a shape: one conversion per constructor per recursive
  definition.

## Log

- 2026-11-02: Step 1 built in review mode. `heather check --review` states
  `f#meaning: f(x̄) = { body }` for every structurally recursive `fn`
  (crates/elab/src/meaning.rs), proves it by splitting the parameter the
  self-calls descended on, gates it inline and rolls it back. A
  `NotConvertible` refusal is the `recursion-meaning` lint's "does not
  unfold to its source"; out of fuel, a refused statement or one that does
  not elaborate is "could not decide". Plans, cheapest first: the recursed
  parameter split 1–5 levels deep along a single recursive field
  (course-of-values windows: `Nat::half` at 2, utf8 `decode` at 5); then
  each parameter the body case-splits on, around it (#389's `inner`, whose
  outer split is evaluated outside the recursor). Branching types split one
  level only (a deeper split is exponential: `Tm::open_at` exhausted the
  rail before the cap). The call is the positional one a caller writes, so a
  constraint's dictionary is resolved, not passed (`mconcat`, the
  `MonoidRel`/`Ring` section functions).
  crates/elab/tests/recursion_meaning_check.rs reproduces the stale-let and
  #389 varied-branch miscompiles with the planner switched off
  (`skip_recursion_plan`, test-only), shows each computing the wrong value
  by `refl`, and shows both reported.

  **Library report (whole `lib/`, review mode):** no definition differs. What
  remains undecided is listed below; step 2 (a refusal) waits on it.
  - Out of fuel (8): the large tactic metaprograms `attempt_from`, `rt_go`,
    `Act::traced`, `solutions`, `mono_class_carrier`, `mono_prove`,
    `norm_num_reify`, `interval_reify`. The equation is one δ step on each
    side; the cost is conversion over their bodies.
  - Not stated (2): `Stmt::weights` (its body calls a local helper,
    `bump_all`, that the restated body cannot see) and `Scope::nodes` (the
    recursed parameter's type is not one the split can name).
- 2026-11-06: Step 2: a refusal. Re-ran the whole-library report on master
  (after recursion at the top, #416/#428): still no definition differs;
  `attempt_from` now settles, so nine were undecided.
  - The two "not stated" (`Stmt::weights`, `Scope::nodes`) were the check's
    own bug: the restatement rewrites a member's base name to its qualified
    name, and both have a parameter of that name (`weights`, `nodes`), which
    was rewritten too. A parameter now shadows the base name
    (`qualified_source`); both hold.
  - The seven out of fuel are cost, not refusals (both mono ones hold at 16×
    the conversion budget): a `match` on a value bound by `let v <- …`
    checks every arm against `Bind::seq`'s β-redex carrier, which
    [[tier2-type-code-functions]] owns (measured there).

  With the check on (`heather check --meaning-check`,
  `Elaborator::set_meaning_check`), it runs on every structurally recursive
  `fn` (at the top, structural, and the at-top fallbacks), and a
  `NotConvertible` refusal of `f#meaning` is the declaration's error, located
  at it. An unsettled check (out of fuel, not stated) refuses nothing; review
  mode reports it as the `recursion-meaning` lint. With the check off, review
  mode reports a difference as the lint, as before. The two negative
  controls are now refusals (`crates/elab/tests/recursion_meaning_check.rs`).

  **Off by default, for cost.** `scripts/perf ab` (cold, calc_parser
  showcase, check on vs master): every counter moves, the kernel gate
  roughly triples and the wall time roughly doubles. Nearly all of it is
  checks that *hold*: `grind`/`tactic` metaprograms (`first_of_among`,
  `apply_holes`, `grind::build`, …) whose bodies are `let v <- …; match v`
  chains, each arm checked against `Bind::seq`'s β-redex carrier
  ([[tier2-type-code-functions]]), paid once more by the restated body and
  once per pair of arms the conversion compares. Next: land
  [[tier2-type-code-functions]], re-measure, and flip the default if the
  check's share is then small; until then a library lane with
  `--meaning-check` is the protection. Step 2's other acceptance (the
  library passes in refusal mode) is recorded below.

  **Library in refusal mode:** `heather check --meaning-check --expectations
  lib` passes (every expected refusal matched, no definition refused), so
  step 2's acceptance holds; the open part is the default.
