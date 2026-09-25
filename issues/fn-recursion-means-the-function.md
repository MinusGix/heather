---
title: Make the refused recursion spellings mean what they say
status: open
labels: [elaboration,recursion,design]
created: 2026-09-25
updated: 2026-09-25
---

Since 2026-09-25 the elaborator **refuses** a structurally recursive `fn`
whose compiled meaning would differ from its source
([[recursive-arm-reads-outer-scrutinee]]). It refuses:
- the decreasing parameter named inside its own recursive `match`, directly,
  through a `let` bound from it above the match, or through a `have` bound
  above it;
- a recursive `match` that is not the body's result;
- a recursive `match` under a branch that depends on its parameter.

Each is safe to refuse because it was wrong to accept. Some of the refused
spellings are the natural way to write the program, though, and `decreases`
is the only escape hatch today. This issue owns making them mean what they
say.

## Two steps, cheapest first

1. **The parameter inside its arm, for `Nat`.** In each arm of the recursive
   `match`, replace the parameter's variable by the arm's constructor term
   (`Zero`, `Succ(k)`) after elaborating the arm. That is sound when no later
   binder's type mentions the parameter (otherwise keep refusing). A `let`
   bound from the parameter above the match is inlined, so the same
   substitution fixes it. A `have` above the match stays refused, since its
   value is computed once. After `Nat`, the same for `Wf`, indexed and forded
   families, where the constructor term is the route's own encoding.
2. **Lower the recursion at the function.** Put the eliminator at the body's
   root and elaborate the whole body once per constructor, with the parameter
   aliased to that constructor. A `match` on it then selects its arm
   statically, and a self-call is the hypothesis wherever it occurs. This
   fixes every refused shape, including code around the match and `have`s
   above it, like `decreases` does today. The price is elaboration and term
   size scaled by the constructor count around the match, and every route
   (`Nat`, `Wf`, indexed, forded, mutual, course of values, generalization)
   reworked.

Step 2 is worth it only if the tail restriction proves annoying in the
library. Record the refusals met in practice here.

**Known gap in the refusal, also owned here:** a type-valued `fn` (`fn
Mem(…) → Type`) elaborates its recursive `match` by a path the expression
dispatcher does not watch, so it is not checked. Either step closes it by
construction; until then, a recursive type family that names its parameter
in its own arm would still compute the wrong type.

## Acceptance (step 1)

- `fn sum(n) { match n { Zero => 0, Succ(k) => add(sum(k), n) } }` is
  accepted, and `sum(2) = 3` holds by `refl`. The same through `let m = n`
  above the match. `Zero => n` gives `Zero`.
- The literal-argument and neutral-argument axes, and the course-of-values
  chain (`n` two levels down).
- The refusals that remain keep their messages
  (`crates/elab/tests/recursion_meaning.rs`).

## What it assumes from elsewhere

- **[[recursive-arm-reads-outer-scrutinee]]** owns the diagnosis and the
  refusal. Assumed here: only that the refusal is the current behaviour, and
  that `Cx::recursion` marks the arms of the recursive `match`.

## Log

- 2026-09-25: Probe (debug and release CLI; the probe files are in the session scratchpad): can the refused shapes fall back to `decreases` instead of being refused, and do they then get a usable `f_unfold` (docs/decreases-unfolding-design.md)? Each shape was written with `decreases <param>` (or `decreases xs.len()`). The test was that it computes by `refl` at a literal and that its `f_unfold` can be cited at a symbolic argument (`sum_unfold(Succ(k))` against `sum(Succ(k)) = plus(sum(k), Succ(k))`).

  | Shape | Computes | `f_unfold` |
  |---|---|---|
  | parameter in its own arm (`plus(sum(k), n)`) | ✓ | ✓ |
  | parameter in the base arm (`Zero => n`) | ✓ | ✓ |
  | `let m = n` above the match | ✓ | ✓ |
  | `have m = n` above the match | ✓ | ✓ |
  | two levels down (course of values, `omega` obligation) | ✓ | ✓ |
  | list, `decreases xs.len()`, `List<Nat>` and `List<A>` | ✓ | ✓ |
  | match inside an expression (`plus(1, match n {…})`, `plus(match n {…}, n)`) | ✓ | **✗** "a `match` holding a recursive call inside an argument" |
  | let-bound match (`let r: Nat = match n {…}; plus(r, 1)`) | ✓ | **✗** "a recursive call in a `let` right-hand side" |

  So **every M1 shape** (reading the top call's parameter) falls back cleanly: right meaning, and an unfolding equation to reason with. **Every M2 shape** (the match not at the root) computes correctly but gets no equation. The generator's §3 fragment excludes exactly those, so a fallback there would give a function nobody can prove anything about at a symbolic argument. Evaluation cost is a constant factor: `tri(60)` by `refl` takes 431 evaluation steps structurally and 1,766 under `decreases` (release, width one).

  The fallback therefore fits M1 (in place of its refusal). M2 either stays refused, or waits for the generator to accept a match holding a self-call in an argument position or a `let` right-hand side. That is its own extension of docs/decreases-unfolding-design.md §3, or step 2 above, which fixes M2 by construction.
