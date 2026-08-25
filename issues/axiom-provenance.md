---
title: "Make axioms explicit and report their transitive provenance"
status: closed
labels: [frontend,proofs,tooling,diagnostics,design]
created: 2026-08-20
updated: 2026-08-24
---

Heather needs a principled way to state irreducible assumptions such as
function extensionality or excluded middle and to answer not only “which
axioms does this theorem depend on?” but “through which declarations did each
axiom enter?” A flat set is useful but opaque: when a high-level result reports
`Classical.choice`, the maintainer should be able to inspect the shortest or
most relevant dependency path back to the importing theorem or instance.

There is no surface `axiom` or `postulate` declaration today. The kernel's
global context can contain a typed binding with no body, while an ordinary
Heather theorem always has a source body that is checked and then stored
opaquely for later use. Design the surface/trust boundary first: an axiom must
be visibly distinct from a proved theorem, impossible to introduce by an
accidentally empty proof, and easy for packages or policy checks to reject.

Track provenance while declarations are elaborated, before theorem opacity
erases proof structure. Each declaration should retain the direct globals its
checked body referenced and the transitive axiom set derived from them. Reports
then reconstruct paths from the dependency graph rather than attempting to
unfold opaque theorem proofs later.

## Surface and policy questions

- Is `axiom name(...): T;` the right explicit declaration, or should assumptions
  live in a visibly imported module/package manifest?
- Are axioms permitted everywhere, restricted by package policy, or rejected
  by default outside designated modules?
- How are generated declarations, instances, theorem-valued record fields, and
  imported cached modules represented in the dependency graph?
- Does changing provenance invalidate caches even when a declaration's public
  statement is unchanged? It should if the cache promises an axiom audit.

## Acceptance

- Specify and implement one explicit surface route for an axiom; ordinary
  `theorem` continues to require a kernel-checked body.
- Reject duplicate/ambiguous assumption spellings and identify axioms clearly
  in diagnostics, listings, and generated documentation.
- Record direct declaration dependencies during elaboration and compute the
  transitive axiom set for every public theorem/function/instance.
- `heather axioms <target>` reports the set plus at least one deterministic
  provenance path per axiom; JSON output exposes the full usable graph or a
  stable queryable slice.
- Reports distinguish primitive/kernel assumptions, user axioms, and ordinary
  opaque theorems.
- Controls cover an unused imported axiom, two paths to the same axiom,
  re-export/qualification, instances, generated declarations, and a theorem
  whose transitive set is empty.
- A project policy can fail checking when forbidden axioms reach selected
  modules or declarations.

## What it assumes from elsewhere

- **[[modules]]** owns declaration identity and import visibility. Assumed
  here: provenance keys declarations by resolved identity, never basename.
- **[[parallel-checking-and-caching]]** owns cached declaration artifacts.
  Assumed here: an artifact can carry provenance metadata covered by the same
  validity/integrity boundary.
- **[[ai-facing-tooling]]** owns the general structured-output principle.
  Assumed here: axiom paths are data first and prose rendering is layered over
  them.

## Log

- 2026-08-24: Follow-up design filed as
  [[implicit-logical-assumptions]]: make assumptions ordinary implicit proof
  or class parameters, let scoped axioms discharge them as a fallback, and
  attach provenance to the caller where that choice is made.

- 2026-08-24: Landed complete (`docs/axiom-provenance-design.md`): explicit
  bodiless `axiom` declarations; body-time dependency capture at the
  `PendingDecl`/commit boundary; deterministic shortest transitive paths keyed
  by resolved module identity; instance and generated-declaration propagation
  with transactional rollback; `heather axioms <target>` text/JSON inspection;
  `check --deny-axioms`; and a distinct cache-interface domain for assumptions.
  Controls cover unused and clean declarations, two paths, qualification,
  synthesized instances, failed generated bundles, and axiom-to-theorem cache
  invalidation. Heather has no generated-doc command today; the public report
  data is the single source a future renderer consumes rather than a parallel
  table.

- 2026-08-20: Filed after auditing the current surface. Heather has no
  `axiom`/`postulate` item; bodiless globals exist in the kernel representation
  and tests, while every source theorem requires a body. The issue therefore
  owns honest introduction as well as dependency reporting.
