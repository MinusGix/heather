---
title: Write unifier solutions in one place that checks their type and agreement
status: closed
labels: [unification,inference,elaboration]
area: language
created: 2026-11-02
updated: 2026-11-03
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

## Log

- 2026-11-03: Built. `unification::assign` is the unifier's one write
  (the `El` rule and the term rule both go through it). An open slot takes
  a solution only if `U::admit` lets it, which is `SolutionCheck`
  (crates/elab/src/solution_check.rs). The check holds the solution to the
  slot's declared type whenever that type is meta-free at the write, and
  judges the slots whose type was still open when the read ends (undoing
  misfits then). Sort-typed slots are not judged, and a solution the kernel
  cannot type or a conversion out of fuel keeps the write. Every caller
  that knows its slots' types passes them: argument reads, the
  expected-type harvest (both routes, including the LGG trigger's), the
  tactic host's `match_at`/`match_dictionaries`, and the bare polymorphic
  argument. The host's holes and `view_instance` have none and convert
  their whole pattern afterwards. `reject_ill_typed_solutions` and its
  mark/undo are deleted, and `unify_root` returns whether a write was
  refused, which drives the δ-reduct retry. A solved slot met again by an
  argument's own type with another subject is reported to `U::disagree`.
  It is kept raw beside the argument's owed comparison (`SlotClash`) and
  spelled only if the gate refuses: "`A` was inferred as `Nat` from an
  earlier argument, and this argument's type would make it `Flag`"
  (crates/elab/tests/unifier_checked_assignment.rs). The new counter
  `solution_checks` counts the kernel-judged writes.
