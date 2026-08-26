---
title: Decide whether finite reachability should expose or squash its fuel
status: open
labels: [stdlib,logic,semantics,proofs,design]
created: 2026-08-26
updated: 2026-08-26
---

`Reaches(R, a, b)` currently exposes an existential fuel and its exact `Steps`
derivation.  That witness is useful for induction and certificates, but it
also makes reachability proof-relevant when many path lengths reach the same
state.  A proposition-facing API could instead squash the existential while
retaining `Steps` for witness-sensitive clients.

Exercise both forms against finite execution concatenation and one certificate
consumer.  Keep the current definition, replace it, or provide both under
names that make witness visibility clear; no change is required unless the
client proofs demonstrate a real distinction.

## What it assumes from elsewhere

- **[[relational-semantics-refinement-kit]]** owns `Steps` and `Reaches`.
- **[[squash-library-api]]** owns the available propositional-truncation tools.
