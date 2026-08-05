---
title: Bare constructors resolved by the expected type in checking position
status: open
labels: [frontend, elaboration, ergonomics, modules]
created: 2026-08-05
updated: 2026-08-05
---

The follow-up `docs/modules-design.md` §4 promised an owner for: in
checking position the expected type names the inductive, so a bare `None`
at expected `Option<A>` is unambiguous whatever is in scope — the
bidirectional elaborator already holds the evidence. Synthesis position
keeps requiring uniqueness or qualification (`Option::None`).

This is the third instance of the one-resolution-judgment direction (doc
§8): `.` fields/methods are receiver-directed, match arms are
scrutinee-directed (landed with v1 — arms position within the scrutinee's
declaration), and this is expected-type-directed. It is also what finally
deletes the historical "constructor names globally unique" constraint
rather than merely scoping it per-module.

Bounded by the doc's two invariants: checking position may *shrink* the
candidate set, never reinterpret — a bare constructor that checks today
must mean the same declaration after any import is added.

## When

Triggered: the first time a real file has to qualify a constructor that
checking position already determines — or the notation/typeclass round,
which wants the same judgment for operators and should build them
together.

## What it assumes from elsewhere

- **[[modules]]** owns the name regime and the qualification escape
  hatch. Assumed here: only that `Type::Ctor` qualification stays.
