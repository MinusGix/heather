---
title: "Operators, methods, and calc for the surface"
status: open
labels: [frontend,syntax]
created: 2026-07-23
updated: 2026-07-23
---

The ergonomics layer the sketches use freely and stage 1 lacks
([[surface-syntax]] rounds 1–3): infix operators, method-call syntax, and
`calc`. Stage-appropriate slice — full traits are NOT needed for any of
this ([[compile-typeclass-design]] owns resolution policy); a fixed
name-directed resolution does for now.

- **Operators**: `+` → `add`, `*` → `mul`, `<` → `lt` (fixed table first;
  the decorated-operator grammar `+_Z` / `⟦R⟧_s` and its trait hookup come
  with the real trait design). `==` already exists as the Id former.
  Precedence: the boring standard one, written down once in the parser.
- **Method calls**: `x.f(args)` resolves `f` in the namespace of `x`'s
  head type former (`p.sym()`, `xs.len()`, `add_zero(n).cong(Succ)`).
  With [[elab-stage2-metas]], the receiver feeds inference so endpoint
  arguments vanish.
- **`calc` blocks** (surface-v1 §1): chained `== rhs := proof` steps
  desugaring to nested `trans` with the step endpoints as the intermediate
  terms — a documented mechanical lowering, no new kernel anything. Wants
  operators for readability and stage-2 inference for the endpoints, but
  neither is a hard blocker.
- Parsing note recorded in the sketches: parenthesized type application
  keeps `<` unambiguous as comparison.

Acceptance: add_comm's Succ arm written as a `calc` block reading like
surface-v1 §1; the Nat suite in method style green alongside the
call-style spelling.

## Log

- 2026-07-23: Opened as part of the granular issue split after stage 1.
