---
title: Lightweight proof automation: auto-refl and apply
status: open
labels: [frontend,elaboration,syntax]
created: 2026-07-24
updated: 2026-07-24
---

Two ergonomic surface features (user-requested 2026-07-24; not scheduled). Both are the *same* underlying move — goal-directed elaboration, the elaborator supplying a proof for a goal it can see — so they are the ergonomic front of the goal engine [[goal-holes]] builds (a hole = an [[elab-stage2-metas]] metavariable that survives to end-of-block). Kernel-safe throughout: the elaborator is untrusted, so a wrong auto-fill is a kernel rejection or an unfilled-goal listing, never unsoundness. Filed together because they share that substrate and were requested together; split if they diverge.

## 1. Auto-refl (trivial-closer for empty/residual goals)

Goal: `theorem two_two(): 2 + 2 == 4 {}` auto-passes — an empty proof block discharges by reflexivity/computation.

- **Mechanism**: in *checking* position, an empty block (later: any residual `?_`) gets ONE speculative `refl` attempt — construct `Refl`, run the existing checking path, keep it iff the kernel accepts; else the goal stays open (-> the goal-listing error from [[goal-holes]]). It is the simplest hardwired instance of that issue's future solver slot (`on _: _ := solver(goal)`).
- **'ignored for values' falls out**: refl only shapes an `Id` goal, and checking-only means a `fn` result type (not generally an equality) offers nothing to close — no default fires in value position.
- **OPEN — conservative vs aggressive**: conservative = speculation is tied to the *empty block / explicit hole* ('I didn't write a proof' is the trigger). Aggressive = `refl` itself becomes a tolerant 'trivial' that silently no-ops wherever inapplicable, so it can be sprinkled. RECOMMEND conservative: a load-bearing `refl` silently doing nothing hides mistakes (Lean's `rfl` errors for exactly this). Record the aggressive reading, do not default to it.
- **MVP is independent**: empty-block -> refl-attempt needs only a parser tweak (allow `{}`) + a checking-position elaborator hook; no [[goal-holes]] engine required. Could land opportunistically.

## 2. `apply` (prefix application threading the continuation)

Goal: `apply sym` reads more naturally than `sym(...)`; 'wrap everything after this'. `apply f` = `f(<continuation>)`.

- **Cheap slice (single continuation)**: `apply sym; apply cong_succ; ih` desugars to `sym(cong_succ(ih))` — pure parser sugar like `calc`, top-down reading (outer step first). Continuation lands as the *last* argument, so stage-2 implicit endpoints infer from it — a prefix mirror of method-calls (receiver-last). Callable-agnostic: `apply Succ; ...` = `Succ(...)` ('support values').
- **Full slice (multi-premise f)**: `apply trans` leaves TWO goals -> `f(?g1, ?g2)` with holes discharged by `on`. This needs the [[goal-holes]] engine; it is 'a more specific kind of defer' — defer f's arguments.
- **OPEN — which premise gets the continuation**: lean 'last explicit premise' (matches method-receiver-last, feeds implicit-endpoint inference); other premises become `on`-discharged holes. Decide against [[surface-syntax]] taste.
- **Dependency**: even the cheap slice wants **block-statement surface** (`apply f;` then more) — blocks are currently single-expression; that statement grammar arrives with [[goal-holes]]. So `apply` is downstream of goal-holes in a way auto-refl's MVP is not.

## Sequencing

Both want [[goal-holes]]' block-statement + `on` surface for their full form; interacts with [[match-recursion]] (self-call proofs share the block surface). auto-refl's empty-block MVP is the one independent, tiny piece. Enabled by [[elab-stage2-metas]] (done). Tracked in [[frontend-roadmap]]; not in the current focus order.
