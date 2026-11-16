---
title: "LSP: what the meta-layer can tell an editor directly"
status: open
labels: [tooling, metaprogramming, design]
area: language
created: 2026-07-24
updated: 2026-08-25
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
  statement is contextual type code (docs/archive/surface-v3.md §2). The
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

## Assumption-aware discovery

The editor presentation of theorem search should show the requirement delta
owned by [[lemma-selection-and-search]], not a binary constructive/classical
classification. A completion or hover can distinguish compactly:

```text
result                    ready
result                    needs Stable<P>
result                    needs ClassicalOn<A>
result                    uses axiom host_conformance
```

Profiles are expanded implicitly for this display through the same resolution
judgment as elaboration. Thus a theorem returns to normal positioning inside
an `assuming classical` environment, and a narrow local proof makes it normal
without requiring that environment. Outside either context it is down-ranked,
not hidden: the missing requirement may be trivial for the user's special
case.

Useful editor actions follow the data rather than the word “classical”:

- prove the exact missing proposition here;
- add an ordinary requirement to one declaration or `assuming` to an item group;
- activate an existing constructive provider with `using`;
- select an axiom-backed provider as an explicit trust escalation.

The last action must display its provenance impact before editing. Whether an
interface is broad, indexed, or constructively implemented is derived from
the real requirement/provider graph; profile annotations for subjective
“triviality” or “nonconstructiveness” wait for evidence that this data is
insufficient.

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
- Assumption-aware ranking is computed once by
  [[lemma-selection-and-search]] and serialized in the structured form shared
  with [[ai-facing-tooling]]; the LSP owns only its editor rendering and
  actions.

`salsa`-style incrementality is the *other* half of an LSP and is orthogonal
to all of this; it becomes interesting only once something re-checks on
keystroke.

## Log

- 2026-08-25: Added assumption-aware discovery: display the exact requirement
  delta, implicitly expand profiles through the real resolver, down-rank but
  never hide unmet candidates, and make axiom-backed `using` an explicit
  provenance-bearing editor action.
- 2026-11-05: gardener: cites a file it shares with [[nested-goal-discharge]] (`docs/archive/surface-v3.md`).
