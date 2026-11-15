---
title: let mut, :=, for, while and early exit in pure functions, lowered to folds
status: open
labels: [frontend,syntax,elaboration,ergonomics]
area: language
milestone: [lang-sequencing]
created: 2026-10-31
updated: 2026-11-02
---

Round R3 of `docs/native/compiler-milestones-proposal.md` (§3.1, §3.3, §7): local state and loops in pure functions.

## Scope

Against `docs/language/sequencing-surface-design.md` (§4–§9, §12), in two slices:

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

- 2026-10-31: R3b's unfolding dependency is now [[unfolding-through-convoyed-match]]; R2's annotated per-variable join loses its required annotation with [[match-infers-constant-motive]].
- 2026-11-01: Layer 1 landed ([[binding-statements]], docs/language/sequencing-surface-design.md §13): the lowering is in the parser's continuation walk (try_lower.rs), scoped per block. Statement if/match here needs the join points of [[bind-in-non-tail-match-arms]].
- 2026-11-02: First R3a slice built (docs/language/sequencing-surface-design.md §14): let mut, :=, statement if/match with optional else and else-if (parser, staged per-variable joins, residuals for enclosing scopes), and for over lists lifted in the elaborator to f::step/f::State over foldl, with captures, nested loops and f_unfold. Open here: break/continue/return, ranges, labels, while, carrier-scope loops, field-path assignment, mut self, the invariant theorems, and wc's step (its split_all; omega facts hit [[split-all-nested-if-omega-kernel-refusal]]).
- 2026-11-02: Early exit built (docs/language/sequencing-surface-design.md §15): break/continue/return in a for body, lowered in tail position by the parser and lifted to ForStep leaves over List::for_in; a returning loop splits the body (`match #forN { Return(r) => r, _ => rest }`), and a stateless search is a loop with an empty state record. Refused at parse time: exits outside a loop, code after an exit, and return from a loop nested in another loop or statement form (needs §6.3). Still open: labels, nested return, ranges, while, carrier-scope loops, field-path assignment, mut self, the invariant theorems, wc's step.
- 2026-11-02: `while c decreases m { … }` built (docs/language/sequencing-surface-design.md §16), reusing the for marker. It lifts to a decreases `f::run` with the state as separate parameters, the body hoisted in SSA form above `match h: decide_bit<c>()`, and `f::run_unfold`. Fixed on the way: select_scope keeps an arm's equation for an argument passed through a let. Filed [[decreases-shadowed-let]]. Open for R3b: exits in a while, the fuelled form, a while holding a for, and the decimal formatter as a while.
- 2026-11-02: Ranges built (docs/language/sequencing-surface-design.md §17): `for i in a..b` is List::range_from(a, b - a), and `0..n` is List::range(n), both written only in a for header.
