---
title: A module using runtime fn must import what the generator looks up
status: open
labels: [native,compiler,metaprogramming]
area: heather-in-heather
milestone: [nh-front]
created: 2026-11-04
updated: 2026-11-04
---

A module that writes `runtime fn f` must also import `tactic`, `char`,
`string`, `rt`, `rt_lower`, `function_ir`, `function_ir_eval` and
`runtime`: the generator spells its output with `lookup(name)`, which
resolves in the module being checked, so every name it publishes through has
to be in that module's scope. Every example in `examples/x86-native` now
carries the eight lines (docs/native/runtime-fn-setups-design.md §16.9). Without
`tactic` the refusal is "`generate` runs a value of the `tactic` protocol";
without the others it is the generator's own "`X` is not in scope".

## Scope

A generator should resolve its own names in its own module (where
`runtime` is defined), not the caller's: a lookup scoped to the
generator's module, or `import runtime;` bringing what `runtime` needs
with it. Related: [[generator-name-scope-follows-last-module]] (closed;
the Rust side of the same trap), [[scoped-declaration-generators]].

## Acceptance

- `import bitvec; import runtime;` is enough to write `runtime fn f`.
- The examples drop the extra imports.
