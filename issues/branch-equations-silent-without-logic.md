---
title: A decreases function's branch equations and induct are silently skipped without import logic; the refusal says it is not a recursion
status: closed
labels: [tactics,elaborator]
area: tactics
created: 2026-11-24
updated: 2026-11-24
---

Found proving the word map's specification ([[runtime-hash-map-spec]]).
`lib/native/runtime/word_map.hthr` first imported only `runtime_data`. Its
`decreases` functions got `f::unfold`, but no branch equations, no
`f::step` and no `f::induct`, and a use reported "`WordMap::find_at` is not
a recursive function whose body is a tree of tests". Adding `import
logic;` and `import bool;` built them all (bisected: dropping `logic`
alone loses them again). `elab_step_equations` records a refusal naming
the missing `bool::Bool::convoy_true`, but the importer's lookup never
reaches it, and the principle's own refusal is not recorded where the
`induct` step reads it (crates/elab/src/declarations.rs, the `recorded`
lookup around `demand_principles`).

## Wanted

The refusal names what is missing ("`f::induct` was not built: this
module needs `import logic;`"), as the step equations' refusal already
does; or the names the equations are built from are reached by their
qualified names, as the runtime generator reaches `rt_held`'s, so a module
need not import them.

Cost note: once built, the companions made `word_map.hthr`'s cold check
several times longer (seven functions' equations and principles).

## Log

- 2026-11-24: 2026-11-24: Fixed (a2df32f). Bisected again: `bool`'s names were reached
  already (a qualified name resolves through the import closure,
  `names::closure_reaches`); what failed without `import logic;` was the
  generated `¬P`, spelled `P → False` with a bare `False`, which outside
  `logic` is the Bool constructor ("`False` cannot be used here"). The
  equations (`branch_equations::not_ty`) and `f::step`
  (`measure::step_equations`) now spell `logic::False`, so a module that
  imports only `runtime_data` gets equations, `f::step` and `f::induct`;
  `word_map.hthr` dropped `import logic; import bool;`. A module that reaches
  neither module is now told `` `bool::Bool::convoy_true` is not reached from
  this module: `import bool;` `` under every designed name, where `induct`
  reads it. In practice every module reaches both (a module with no imports
  does, through the common prelude), so that refusal is a fallback; the
  probe `lib/_tests/std/tactic/induct_unreached_tests.hthr` is a module with
  no imports doing `induct`, and
  `lib/_tests/native/runtime/runtime_data_induct_tests.hthr` the
  `runtime_data`-only module.

  Cost note, measured (one uncached check of word_map.hthr, stopwatch per
  stage): the module is ~165 s, of which the four probes' companions are
  nearly all; the largest single cost is `shift_at`'s `f::induct` (~57 s),
  and within it `measure::lift_found` over the generated principle (~45 s):
  per-query re-elaboration of a 24–26-binder telescope. Equations are ~22 s
  across the four, `f_unfold`/`ext`/`irrel` ~37 s. Filed as
  [[principle-found-proof-lifting-cost]] with the table.
