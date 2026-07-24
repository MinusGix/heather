---
title: "LSP: what the meta-layer can tell an editor directly"
status: open
labels: [tooling, metaprogramming, design]
created: 2026-07-24
updated: 2026-07-24
---

Speculative design note, not a work item — parked so the idea is not
re-derived later. An LSP is firmly after [[cli-check-diagnostics]], but *what*
Heather's LSP could serve is unusual enough to record now, because it may
influence how `Compile`/`runtime_func` are shaped while they are still
being designed.

The ordinary route is: the compiler exposes an API, the LSP calls it, and
the editor renders whatever the compiler's authors thought to expose. The
observation (user, 2026-07-24) is that Heather's compilation story is
*closely linked to kernel-time code*, so a lot of what an editor wants is
already a first-class, well-typed value in the language rather than a
compiler internal:

- **Goal state is already code.** A hole is `u : Trm(Γ ⊢ P)` and its
  statement is contextual type code (docs/sketches/surface-v3.md §2). The
  unfilled-goal listing [[goal-holes]] already renders is not a debug view
  of a compiler data structure — it is a projection of language values.
- **A `Compile` instance carries its own generated IR and its equivalence
  proof** ([[compile-typeclass-design]], [[certifying-generator]]). An
  editor could show, inline against the source function, the code that will
  actually run *and* the certificate that it matches — with no compiler
  surface dedicated to it, because both are ordinary values.
- **`runtime_func`** likewise knows the relationship between the source
  definition and the emitted function, so "what did this compile to, and
  why is that sound" is answerable directly rather than reconstructed.

The interesting consequence: **an editor feature could be a library**. A
meta-function `Code(Γ ⊢ T) → Presentation` is an ordinary typed program;
if the LSP's job is largely to run such functions and ship their output,
then domain-specific IDE views (show me this instance's IR, show me the
optimisation guard that fired and its proof) are written by whoever writes
the domain library, not by whoever writes the LSP. That is the same move as
[[surface-syntax]]'s position on tactics — solvers are ordinary
untrusted-by-construction meta-functions — applied to tooling.

## What to keep in mind meanwhile

- Do not let `Compile`/`runtime_func` bury the source↔IR correspondence in
  elaborator-internal state; if it is a value, the above is nearly free.
- The goal listing's structured form (`GoalReport`) is the prototype of this
  shape: `elab` produces data, the front-end renders. Keep new diagnostics
  on that side of the line ([[dependency-policy]]: rendering lives in the
  CLI).
- Determinism matters here too: an editor view keyed on elaborated syntax
  has the same exposure as any other syntax-keyed consumer
  ([[elaboration-determinism]]).

`salsa`-style incrementality is the *other* half of an LSP and is orthogonal
to all of this; it becomes interesting only once something re-checks on
keystroke.
