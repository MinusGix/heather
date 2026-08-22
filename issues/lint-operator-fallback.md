---
title: "Lint operator uses that resolve only through a basename fallback"
status: closed
labels: [tooling,lint,frontend,notation,resolution,ergonomics]
created: 2026-08-22
updated: 2026-08-22
---

Heather's operator resolution ladder can fall back from a symbol to a
conventional global basename. That compatibility route is useful, but it can
also conceal a missing designation, missing import, or operation being used at
an unintended carrier.

Record the successful resolution route and warn when written operator syntax
reaches the basename fallback rather than a local symbol binder or applicable
designation. The message should name the fallback declaration and suggest the
specific declaration/import step that would make the notation intentional.

This is semantic provenance, not a ban on named calls. A writer who spells
`add(a, b)` asked for that declaration directly and should not receive this
warning. Built-in or deliberately fallback-only operations need explicit
controls or profile treatment rather than hard-coded message exceptions.

## Acceptance

- The lint is driven by the resolver's actual selected route and declaration,
  never by symbol/name correspondence after elaboration.
- Local operator binders and carrier-applicable designations are silent.
- Missing imports, multiple carriers, shadowing, qualification, and first-class
  named operation values have controls.
- The diagnostic identifies the fallback declaration and an actionable way to
  install or import the intended designation.
- The stdlib census determines whether the rule is conservative-default or
  profile-only; rollout does not assume the answer.

## What it assumes from elsewhere

- [[lint-roadmap]] owns that rollout decision.
- [[notation-extensibility]] owns the operator-resolution ladder; this issue
  observes its selected route and does not change precedence or resolution.

## Log

- 2026-08-22: Filed from the lint review as a resolution-surprise diagnostic,
  not merely a canonical-spelling rule.
- 2026-08-22: Implemented `operator-fallback` at rung 3 of the resolver itself.
  It records the selected fallback declaration, carrier, evidence source, and
  span only when the carrier probe found an uncovered carrier; fallback-only
  programs with no designation anywhere retain the compatibility behavior
  silently. Cloned/speculative elaboration cannot leak provenance, failed
  items roll it back, and the stdlib census found zero occurrences.
