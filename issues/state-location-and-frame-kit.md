---
title: Develop state locations, updates, and frame reasoning
status: open
labels: [stdlib,logic,semantics,design]
created: 2026-08-25
updated: 2026-08-25
---

Specifications that update structured state repeatedly need a common way to
name a location, read it, update it, compose nested locations, and prove that
everything outside the write remains unchanged.  Without such a kit, every
instruction or state machine grows bespoke record reconstruction and bespoke
"the other fields are preserved" lemmas—the least interesting and most
error-prone part of an effects proof.

Probe conventional total lenses against a first-order location datatype plus
an interpreter.  Heather can express function-valued records, but equality and
reduction behavior may make the apparently elegant lens encoding expensive;
the first-order route may compose better with reflected code and decidable
syntax.  The round should decide from written proofs, not from terminology.

## Acceptance

- Choose and document the representation of a total readable/writable
  location, including whether locations are functions or first-order data.
- Provide read, write, location composition, and the get-put, put-get, and
  put-put laws.
- Define disjointness or an equivalent noninterference predicate and prove
  write/read commutation for disjoint locations.
- Provide a frame/effect-footprint statement that says which locations may
  change across a state relation, plus composition rules for footprints.
- Exercise a nested record, two disjoint fields, and two overlapping slices of
  one field; the last case must fail or demand the precise side condition.
- Show how partial access (for example a missing memory address) composes with
  total locations without pretending the partial access is a lawful lens.
- Keep architecture register aliases and x86 partial-register rules out of the
  core kit; they are later instances/custom locations justified by this API.

## What it assumes from elsewhere

- **[[relational-semantics-refinement-kit]]** owns generic relations and their
  composition.  This issue owns the state-local frame vocabulary layered over
  those relations.
- **[[fixed-width-bitvectors]]** owns slicing and update facts for bit fields.
  Assumed here only for the overlapping-slice acceptance case; ordinary record
  locations can be developed first.

## Log

- 2026-08-25: Filed with the x86 model as the first large customer, but the
  abstraction is intended equally for interpreters, protocols, and verified
  stateful algorithms.
