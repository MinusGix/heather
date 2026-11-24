---
title: A decreases function's branch equations and induct are silently skipped without import logic; the refusal says it is not a recursion
status: open
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
