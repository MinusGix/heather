---
title: Decide when Unsupported coverage should carry a structured reason
status: open
labels: [stdlib,semantics,diagnostics,design]
created: 2026-08-26
updated: 2026-08-26
---

`Coverage<A, E>` currently has a payload-free `Unsupported` constructor.  This
is enough to keep missing model coverage distinct from normal returns and
specified faults, but operational coverage ledgers will likely need to say
which instruction or feature is absent and why.

Let the first coverage-reporting customer determine whether the generic type
needs a reason parameter, whether the instruction belongs in the reason or in
the surrounding judgment, and which reasons should be structured.  Preserve
the key invariant: an unsupported case must never become a `SemanticOutcome`
or masquerade as an architectural fault.

## What it assumes from elsewhere

- **[[relational-semantics-refinement-kit]]** owns the outcome/coverage split.
- **[[x86-64-machine-model]]** owns the first proposed coverage ledger and is
  the likely trigger for revisiting the payload.
