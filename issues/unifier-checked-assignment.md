---
title: Write unifier solutions in one place that checks their type and agreement
status: open
labels: [unification,inference,elaboration]
area: language
created: 2026-11-02
updated: 2026-11-02
---

`unify_tm` writes a solution at one line (`sols[i] = Sol::Solved(s)`,
crates/elab/src/unification.rs:580) with a scope check but no type check, and
an occurrence of an already-solved meta is never compared with its solution
(first write wins, silently). PR #387 added `reject_ill_typed_solutions` after
whole reads, at two call sites (`unify_arg_ty`, `solve_from_expected`), for
Π-typed slots only, by snapshotting `Unsolved` marks and undoing. The other
callers of `unify_root`/`unify_under` (`host.rs` ×3,
`application/polymorphic.rs`) are unchecked.

## Proposal (P1 of docs/elaborator-principles-survey.md)

One `assign(i, s)` used by every write:

- scope and occurs check (today's strengthening);
- the solution's type converts with slot `i`'s type whenever that type is
  meta-free after zonking (not only Π slots); refuse the write otherwise;
- an occurrence of a solved meta compares its solution with the subject.
  Still learn-only (it never fails the call), but a disagreement is recorded,
  for the diagnostics and as the local trigger [[unifier-lazy-delta]] wants.

`reject_ill_typed_solutions` and its mark/undo at the call sites are then
deleted.

## Cost and risk

A kernel `infer` + `convert` per solution on the elaborator's hottest path,
so this round measures with `scripts/perf ab` (CLAUDE.md: a new inference
route on a hot path). Cheap paths first: compare heads (a global's type is a
lookup), skip sort-typed slots. Behaviour risk is low: a wrong-typed
solution could never be corrected later, so calls that elaborate today keep
their solutions.

## Acceptance

- #387's probes (rat_tests, dyadic_tests) pass with the post-hoc check
  removed.
- A probe where a meta occurs twice with disagreeing subjects reports the
  disagreement instead of the downstream type mismatch.
