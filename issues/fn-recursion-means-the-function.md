---
title: Make the refused recursion spellings mean what they say
status: open
labels: [elaboration,recursion,design]
area: language
created: 2026-09-25
updated: 2026-11-07
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

- 2026-09-25: Probe (debug and release CLI; the probe files are in the session scratchpad): can the refused shapes fall back to `decreases` instead of being refused, and do they then get a usable `f_unfold` (docs/language/recursion/decreases-unfolding-design.md)? Each shape was written with `decreases <param>` (or `decreases xs.len()`). The test was that it computes by `refl` at a literal and that its `f_unfold` can be cited at a symbolic argument (`sum_unfold(Succ(k))` against `sum(Succ(k)) = plus(sum(k), Succ(k))`).

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

  The fallback therefore fits M1 (in place of its refusal). M2 either stays refused, or waits for the generator to accept a match holding a self-call in an argument position or a `let` right-hand side. That is its own extension of docs/language/recursion/decreases-unfolding-design.md §3, or step 2 above, which fixes M2 by construction.
- 2026-09-25: LANDED: the measure fallback, with the refusal machinery replaced (docs/language/recursion/termination-measures-design.md §7). Full suite 2989 passed, 0 failed.
  - **Reads of the parameter now compile by measure** instead of being refused: directly, through a `let` or `have` bound above, in the base arm, or two levels down. The declaration is lowered as if it said `decreases p`, or `decreases p.len()` for a `List`, with `omega` discharging the obligations. It computes the source's value and has a usable `f_unfold`. A `recursion-by-measure` note names what is lost (definitional unfolding at a symbolic argument) and the spelling that keeps the structural lowering. Without `nat`/`int`/`omega` in scope, or at a parameter that is neither `Nat` nor `List`, it is refused with what to import or write.
  - **A match off the result or under a dependent branch is still refused**, at the first self-call actually lowered under it. The generator's §3 fragment has no equation for those shapes.
  - **Mechanism:** one surface pass, `recursion::plan`, which is binder-aware and tracks which parameters every visible name depends on. `elab_decl` routes on its answer. The only elaborator state is one per-declaration slot (`misplaced_recursion`, keyed by the recursion name), read in `elab_self_call`. The `Cx` tail spine, the recursion scope, the name-resolution hook, the dispatcher hooks and the error-path substitution of the previous round are gone. `surface::for_each_child` factors `walk_expr`'s child iteration. `SelfRef::of_decl` is shared by the planner and the body.
  - **Tests:** `crates/elab/tests/recursion_meaning.rs` moved to the `omega` family, so it has the measure route: 10 tests, each accepted case pinned by what it computes.
  - **Remaining here:** make the off-result shapes legal (extend the §3 generator for a match holding a self-call in an argument or a `let` right-hand side, or step 2's per-constructor lowering), and measures for declared inductives other than `List` (a derived size). The type-valued `fn` gap noted above is closed, because the plan is syntactic and sees every `fn`.
- 2026-11-02: Found a sibling miscompile this issue's refusals do not cover: a `let` above the recursive `match` bound from a parameter the self-call changes keeps the top call's value ([[recursion-let-reads-changing-parameter]]).
- 2026-11-04: 2026-11-04: For `Nat`, the parameter read inside its arm (or through a `let`/`have` above the match) now lowers by recursion at the top ([[recursion-below-nat-fallback]]), which means the source and unfolds by conversion; the measure lowering is the fallback where that does not elaborate (calls two below, an implicit varied). `List` and the misplaced-match spellings at other types are unchanged.
- 2026-11-05: gardener: cites a file it shares with [[frontend-roadmap]] (`docs/language/recursion/termination-measures-design.md`); [[omega-renders-member-by-base-name]] (`docs/language/recursion/termination-measures-design.md`).
- 2026-11-07: step 2 (the recursion at the function) now covers tier-1 `Wf`
  too ([[recursion-at-top-wf]]): the parameter in its arm, a `let` above the
  match, and a `match` off the result (in an argument, a `let` right-hand
  side) lower at the top for `List` and declared tree types, by `refl` at a
  literal and an open argument. Left: indexed, `IWf`, forded and mutual
  families, which keep the refusals and the measure route.
