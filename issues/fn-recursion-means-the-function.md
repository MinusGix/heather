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
