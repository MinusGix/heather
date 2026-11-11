---
title: A variable's type was weakened from its entry at every use
status: closed
labels: [kernel,elab,substitution,performance]
area: kernel
created: 2026-11-10
updated: 2026-11-10
---

Γ stores a binder's type in the scope it was bound in, and a use `x_i` reads
it `i + 1` binders later, so both the checker's variable rule and the
elaborator's `Elaborator::local` returned `entry.ty.shift_local(i + 1)`: a
fresh copy of every open node of the type, per use. A record's parameters
are used many times each, at a handful of distances, under one context.

## What is built

- **Checker** (`typing.rs` `Tc::weakened`). The variable rule returns a
  deferred syntactic type, and the weakened node is kept per checker by the
  entry's node and the distance (the entry is held, so the address stays its
  node's). One node per `(binder, distance)` also means two uses give
  conversion the same node, which its identity shortcut answers.
- **Elaborator** (`attempt.rs` `DeclAttempt::weakened_entries`, read in
  `Elaborator::local`). The same table, for one declaration attempt. It is a
  pure function of node and distance, so it is kept across probes (`mark`
  and `restore` leave it), and cleared with the attempt.

A projected variable's type is described in the entry's own scope and never
weakened at all (`ITy::At`, [[projection-description-quadratic]]); this is
the plain variable's half.

## Log

- 2026-11-10: Built. Checker half, callgrind inside the showcase's kernel
  gate: 17,335.0 M instructions to 17,204.0 M, and 171 conversion queries
  move from a miss to a memo hit. Elaborator half, `scripts/perf ab` on the
  cold showcase: `resolve` phase 0.89 s to 0.69 s, every sample separate;
  `local_subst_nodes` 21.87 M to 17.02 M. Wall is measured together with
  [[abstraction-walks-the-type-twice]].
