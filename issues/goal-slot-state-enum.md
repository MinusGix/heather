---
title: Goal slot state as one enum (Open/Solved/Proved/Transparent)
status: closed
labels: [elaboration,refactor,state-machine]
area: infrastructure
created: 2026-11-02
updated: 2026-11-02
---

Replace `Goal`'s `solution`/`proved`/`transparent` triple with one state enum.

## Problem

`goals::Goal` (`crates/elab/src/goals.rs` ~29) holds `solution: Option<Rc<Term>>`, `proved: bool` and `transparent: Option<Transparent>`. Of eight combinations four mean something: Open, Solved (by an `on` clause), Proved (a tactic proof lifted to a lemma) and Transparent (a value lifted to a definition). Readers re-derive which: `lifted()` filters `proved || transparent.is_some()` then `expect("a lifted slot is solved")`; `outstanding()` and `reports()` filter `solution.is_none()`; `delta_world` matches `transparent: Some(..)`. Survey: `docs/implicit-state-machines-survey.md` §5.

## Proposal

`enum GoalState { Open, Solved(Rc<Term>), Proved(Rc<Term>), Transparent(Rc<Term>, Transparent) }`, with `solution()`/`is_lifted()` accessors. The unifier made the same move for its metas (`unification::Sol`), replacing a planted `Term::Zero` that made a withheld slot look solved. Small and local; no behaviour change.

## What it assumes from elsewhere

- **[[decl-attempt-lifecycle]]** owns the arena's phases. Assumed here: nothing beyond the slot's own states.

## Related

Filed together from the implicit-state-machines survey (`docs/implicit-state-machines-survey.md`, 2026-11-02, ranked there): [[elab-field-lifetimes-explicit]], [[module-pass-state-machine]], [[kernel-psi-bound-cache]], [[decl-attempt-lifecycle]], [[kernel-checker-mode-enum]].

## Log

- 2026-11-02: LANDED: `GoalState { Open, Solved, Proved, Transparent(term, Transparent) }` replaces the triple in `crates/elab/src/goals.rs`; `lifted()` matches on it (no `expect`), `outstanding`/`reports`/`named` ask `is_open()`, and `Goal::solve` debug-asserts the slot was open. No `is_lifted()` accessor: its only reader, `lifted()`, matches the two lifted states directly. No behaviour change.
