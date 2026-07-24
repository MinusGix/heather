---
title: "Holes and on-discharge (goal-oriented blocks)"
status: closed
labels: [frontend,elaboration,syntax]
blocked-by: [elab-stage2-metas]
created: 2026-07-23
updated: 2026-07-24
---

The goal design of docs/sketches/surface-v1 §2 / v2 §2 / v3 §2
([[surface-syntax]]): named holes `?name` as first-class deferred
obligations, discharged in-block by `on` — with goals literally being the
elaborator's metavariables ([[elab-stage2-metas]] is a hard dependency: a
hole IS a `u : Trm(Γ ⊢ T @ l)` that survives to the end of the block
instead of being solved by unification).

Decided surface (sketches):

- `?name` / anonymous `?` holes; `on ?name := expr;` discharge, any order.
- Default names from the callee's proof-parameter name, ordinal dedup,
  provenance in the listing ("proof-parameter names are API").
- Discharge-by-statement `on _: P := expr;` — discharges *all* goals whose
  statement matches P.
- Auto-holes: an implicit proof parameter marked auto-defer becomes an
  anonymous goal at the call site (`xs[i]` sugar, later).
- NO positional filling; goal merging is hole-programming (v3 §2), not a
  feature.
- Unfilled goals at block end = error listing each goal with provenance —
  this listing is the "checker shows goal state" UX and the tooling face
  of the whole design; worth making good early.

Out of scope here, tracked in the sketches: solver meta-functions
(`on _: _ := solver(goal, …)`, v3 §2) — needs the modal layer surfaced.

## Log

- 2026-07-23: Opened as part of the granular issue split after stage 1.
- 2026-07-24: Related: [[surface-proof-automation]] (auto-refl + apply) builds on this engine — auto-refl is the simplest hardwired instance of the future solver slot; apply's multi-premise form is defer-into-a-specific-application, discharged by on.
- 2026-07-24: Landed. Surface: a real `Block` node — `block := { stmt* expr on_stmt* }` — with `let x (: T)? = e;` bindings (inlined aliases, the `fn`-definition doctrine, not kernel binders) and trailing `on` discharges; `?name`/`?` lexed as one token by adjacency (`?p` named, `? ` anonymous). Elaborator: a goal is a Ψ-global exactly like a stage-2 meta, but decl-scoped — goals take the innermost indices [0,G) for the whole declaration, every committed-global reference is offset by `goal_base` (two sites in `resolve`), and one `GlobalSubst` at the end fills them and renumbers everything back down. Three non-obvious pieces: (a) G is a syntactic *upper bound*, not the count — `calc` clones sub-expressions into its `@trans` spine and some nodes are elaborated twice — so goals are numbered in creation order, deduped by hole span, and unused slots padded; (b) an `on` RHS elaborates *in* the goal world (the goal's Γ and statement live there) but a σ payload is scoped in the source Ψ, so solutions are strengthened back down by G — sound exactly because a hole inside an `on` RHS is refused (`frozen`); (c) `goal_base` covers the telescope and result type too, not just the body, since their types end up embedded in the emitted term. `on _: P := e` matches by kernel convertibility against a padded Ψ (`goal_psi`), P elaborated per goal in that goal's own context, discharging every match; zero matches is an error, not a no-op. Unfilled goals produce one `ElabError::UnsolvedGoals` listing — name, statement, captured context, provenance ("the \`p\` parameter of \`sym\`") — plus the first `Display`/`render(src)` in the tree. Anonymous holes default to the callee's parameter name with ordinal dedup (`p`, `p.1`), so proof-parameter names really are API. MVP restrictions, each with a test: holes are checking-only (rejected in inference position — notably `sym(?p)`, since implicit-taking callees infer their explicit args; write `@sym(a,b,?p)`), one occurrence per named hole, no holes in an `on` RHS, `on` trailing-only. 22 acceptance tests in crates/elab/tests/goal_holes.rs; the money test is a goal raised under a `match` arm discharged at block end using that arm's binders, and the kernel-gate test proves goals do not weaken the gate. No kernel changes.
