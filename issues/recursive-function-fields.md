---
title: Surface inductives with recursive function-typed fields, lowered through W
status: closed
labels: [inductives,elaboration,effects,design]
area: interaction-trees
milestone: [it-function-fields]
created: 2026-10-20
updated: 2026-10-20
---

Owns the roadmap's `it-function-fields` submilestone (`docs/roadmap.md`):
let a surface inductive declare a recursive function-typed field, such as an
interaction tree's continuation `Vis(c: E.Cmd, k: E.Resp(c) -> Tree)`, and
match and recurse over it. Today `reject_function_fields`
(`crates/elab/src/inductive.rs`) refuses it.

This is interaction-tree work, with ITrees as the driving client. The same
lowering also opens surface `Acc` and other infinitely branching types.

## What it assumes from elsewhere

- **[[inductive-compiler]]** owns the tier scheme and says such a field is
  tier 2, W-lowered. Assumed here: only that tier 2 lowers through the
  kernel's `W` former. Acc via W is already kernel-checked
  (`docs/acc-via-w.md`).
- **[[interaction-trees-container-model]]** owns the tree library this
  serves. Assumed here: only that its continuation is a function of the
  response type, with events written as containers.

## Done when

`Vis(c, k)` declares at the surface, with structural recursion through `k`
and a match on the tree, and the generated terms are tested on all four axes
of `docs/testing-generated-terms.md`.

## Log

- 2026-10-20: LANDED (docs/inductive-tier2-w-lowering.md, written before the code; crates/elab/src/infinitary.rs; 15 kernel-checked tests in crates/elab/tests/inductive_tier2.rs). `⟦D⟧ = Σ(t : W(x:S). P). El(canon t)`: tier 1's shape, positions by a case on the label (`Empty`/`Unit`/the field's domain at the label's payload), and a leaf predicate `canon` that makes a leaf's children `f₀` by an `Id` the constructors prove by `refl` and the `match` eliminates with `J`. The predicate is the finding: bare `W` loses the leaf arm of every dependent `match`, since `Π(y : Empty). W` is not a singleton without the initial-object η the kernel declines (§2.1), and interaction trees are mostly leaves. No `Ψ` axiom; constructors stay definitional at open payloads. Recursion through `k` is a self-call at `k(e)` for any `e`, matched by the application's head term, lowered to `(λy. ih' y (c y)) e`. Tested on the four axes: closed computation through `k` by `refl`, β on open `c`/`k`, induction at every kind including the leaf (`first(rebuild(t)) = first(t)`, and `first(bind(t, h)) = first(h(first(t)))` at an open element type), neutral scrutinees stuck, negative controls (a call at a value built around `k(e)`, a false equation under `k`, `rebuild(Vis(c, k)) = Vis(c, k)`), every §1 restriction diagnosed by name, `absurd` and payload `inj`. Boundary recorded rather than worked around: tree laws through `Vis` (`bind(t, Ret) = t`) need funext and are for the depth-indexed equivalence of [[interaction-trees-container-model]], not `=`. Residue: [[tier2-value-parameters]] (ITree's `E` as a value parameter: the occurrence `ITree<R>(E)` is not classified as uniform, at either recursive tier), [[tier2-fragment-extensions]] (curried fields, branching beside a function field, generated definitions, `inj` at a child, windows, certgen/native), [[deep-pattern-dependent-later-field]] (inherited from tier 0, found here: `Vis(Ask, k)` is a kernel rejection).
