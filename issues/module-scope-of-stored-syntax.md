---
title: Stored surface syntax resolves at the use site, not the declaring module
status: closed
labels: [frontend, elaboration, modules, robustness]
created: 2026-08-05
updated: 2026-08-09
---

Found by the modules implementing round (2026-08-05, [[modules]]). An
inductive declaration keeps its field types in **surface** form and
re-lowers them at each use (instantiation, arm walk); that lowering
resolves names against the *importing* module's scope, not the scope the
declaration was written in.

Consequence: if module `a` declares `List` and `b` (which imports `a`)
declares its own `List`, then in a file importing both, an `a::Cons`'s
stored `tail: List<A>` re-lowers against the file's scope — where `List`
is ambiguous or, worse, uniquely the *other* `List`. Today this is loud,
not silent: nominal tags differ, so the mis-resolved lowering fails to
typecheck at the use. But it is a use-site error for a declaration-site
fact, and it violates the growth invariant of `docs/modules-design.md` §8
in spirit: adding a declaration to one module changes what an *unrelated*
module's stored syntax means somewhere else.

Fix shapes, when a round takes it: carry a resolution environment (the
declaring module's `Scope`) with stored surface syntax and resolve against
that; or close stored syntax over its scope at declaration time (resolve
names to `module::name` form once, when the declaration elaborates). The
second is the smaller carry and matches "a name is a reference": the
declaration meant one thing when it checked, and that meaning is what
should be stored.

Documented in code at the `module_scopes` field (`crates/elab/src/lib.rs`).

## When

Triggered: the first time two modules legitimately declare the same type
name and one is used through an import — or the caching round, which has
to serialize stored syntax and should not serialize an open name.

## What it assumes from elsewhere

- **[[modules]]** owns the resolution regime. Assumed here: only that
  resolution is per-module visibility with no import-order precedence.

## Log

- 2026-08-09: LANDED: every Inductive retains its declaration Scope by Rc, and an RAII resolution-scope stack installs it whenever stored value-parameter types, constructor field types, route-1 families, or route-2b result indices are re-lowered. Cross-module collision regressions cover ordinary and recursive fields, match lowering, value parameters, and a computed forded index. Fast and full suites pass.
