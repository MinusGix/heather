---
title: A structural function's induction principle, from a module that imports it
status: open
labels: [proofs,elaboration]
area: language
milestone: [lang-proof-modularity]
created: 2026-11-15
updated: 2026-11-15
---

`f::induct` (`docs/tactics/functional-induction-design.md`) is built with
the function for a `decreases` loop, and on demand for a structural
recursion: at the first declaration of the function's own module that does
`induct f(…)` or names `f::induct`. Building it for every structural
function cost about a third of a cold elaboration of the SHA-256 tree, most
of it the library's large generator functions (`rt_held_do`, `laid_fields`),
which nobody proves about by induction.

So a module that imports a structural function cannot do induction along
it unless the function's module already built the principle: the step
refuses with "a principle is built in the module that declares its
function". `induct List::foldl(…)` from outside `list` is the probe
(`lib/_tests/std/tactic/induct_tests.hthr`).

## Scope

- Build it in the importing module. What is missing is the function as
  written: the stored surface declaration of a function is its signature
  and its lowered form, not the body the equations are read from, and a
  module image carries only signatures. Either images carry the written
  body of a recursive `fn` (an image-format change, Minus's call), or the
  equations are read from something that does survive, such as the
  structural lowering's own recursor arms.
- Two sibling modules that each build `f::induct` for an imported `f` would
  both designate `f::induct`; a module importing both must not refuse that
  (`designate_access` is idempotent on the same minted name, so the minted
  name would need to be the same, or the second lookup would have to prefer
  one).

## Done when

`induct List::foldl(xs, f, z); all_goals { … }` works from a module that
imports `list`, and the probe moves from a refusal to a theorem.
