---
title: let mut, :=, for, while and early exit in pure functions, lowered to folds
status: open
labels: [frontend,syntax,elaboration,ergonomics]
area: language
milestone: [lang-sequencing]
created: 2026-10-31
updated: 2026-11-01
---

Round R3 of `docs/compiler-milestones-proposal.md` (§3.1, §3.3, §7): local state and loops in pure functions.

## Scope

Against `docs/sequencing-surface-design.md` (§4–§9, §12), in two slices:

**R3a.**

- `let mut`, `:=` (also to field paths, via `with`), a statement `if`/`match` with optional `else`, `for` over lists and `a..b` ranges, `break`/`continue`/`return`, loop labels, and `while … fuel n { … } exhausted { … }`.
- Lowering (§5): SSA aliases with per-variable annotated joins, and every loop's body as a named sibling step function (`f::step`, `f::State`, `f::run`; `f::<label>_step` when labelled, ordinals otherwise). `for` is `O::foldl` with no early exit and `O::for_in` with one. `List::for_in` and `ForStep` go into `list.hthr`.
- The same forms in a carrier scope (§6): CPS over `O::foldr`, joins through `bind`, fuel-only `while`. `?` inside a loop is `return Err(…)` (§6.3).
- `mut self` parameters (§8.2): the method returns the pair, and a call on a `let mut` local reassigns it.
- `f_unfold` by `refl` for every function with a layer-2 statement (§7.1). The library theorems `List::foldl_invariant` and `List::for_in_invariant` (§7.2).
- Negative controls from design §10, layer-2 rows.

**R3b.** `while c decreases m { … }` as a generated `decreases` function with the state as separate parameters and the condition under `match h:` (§5.3). Depends on [[unfolding-computed-scrutinee]] for its `_unfold` (probe P5).

Cost as a shape (§12): linear lowering, one condition copy per assigned local per `if`, and each loop body elaborated once as its step's declaration.

## Done when

R3a: `wc`'s step is written imperatively, and its facts are proved by the existing tactics with no hand unfolding. R3b: the decimal formatter is a `while` over `m`, and `decimal_places` is proved against it.

## What it assumes from elsewhere

- **[[sequencing-surface-design]]** owns the lowering.
- **[[loop-invariant-rules]]** owns the invariant rule over these loops.

## Log

- 2026-11-01: Layer 1 landed ([[binding-statements]], docs/sequencing-surface-design.md §13): the lowering is in the parser's continuation walk (try_lower.rs), scoped per block. Statement if/match here needs the join points of [[bind-in-non-tail-match-arms]].
