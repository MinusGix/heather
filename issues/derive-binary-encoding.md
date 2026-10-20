---
title: Synthesize binary encoders from record field instances
status: open
labels: [metaprogramming,serialization,proofs]
area: heather-in-heather
created: 2026-09-07
updated: 2026-09-07
---

## Scope

Make a reusable metaprogram that constructs a binary-encoding instance for a
record whose fields implement the encoding trait. This is a concrete customer
for the common pattern of composing field instances into a checked record
instance, rather than a privileged serializer built into the compiler.

## Acceptance

- Begin with finite flat records and deterministic explicit wire field order.
  Generate ordinary instance terms and required proof terms for kernel checking.
- Resolve each field's encoding instance through the normal mechanism; report
  missing or ambiguous instances at the relevant field.
- Preserve handwritten implementations as an alternative; verify synthesized
  bytes and size laws against an independently specified example layout.
- Define supported schema metadata and diagnose unsupported recursion, unions,
  pointers, and variable-length layouts rather than guessing a representation.
- Demonstrate an ELF record and another small record to establish reuse.

## What it assumes from elsewhere

- [[binary-encoding-trait]] owns the encoding and correctness contract.
- [[generators-in-the-language]] owns the broader generator direction; this issue
  owns only this bounded synthesis customer.
- [[elf64-structured-image]] owns the initial ELF use case and can proceed with
  handwritten encoders before synthesis is available.

- 2026-09-07: Use [[host-elaboration-interface]] and [[scoped-declaration-generators]] for reflection/elaboration and checked instance publication as needed. Initial trait/library work can use independent sample records, leaving ELF integration to its owner.
