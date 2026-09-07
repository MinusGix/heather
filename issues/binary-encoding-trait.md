---
title: Define reusable explicit binary wire-encoding contracts
status: open
labels: [library,serialization,proofs]
created: 2026-09-07
updated: 2026-09-07
---

## Scope

Own a reusable trait/interface for turning supported values into binary wire
bytes, with a logical contract relating the bytes to the format specification.
ELF records are the first customer. This is not host-memory copying or an
implicit promise that every Heather type has a meaningful binary layout.

## Acceptance

- Specify encoding composition for fixed-width primitives and records, with
  explicit endianness, field order, padding, and encoded size.
- Define how lengths, overflow, variable-size fields, and unsupported encodings
  are represented or rejected; do not silently truncate to fit a wire field.
- Support handwritten instances and checked composition. State appropriate
  correctness laws; require decode round trips only where a decoder is defined.
- Demonstrate an ELF record instance and byte/size laws, including boundary cases.
- Keep native ABI representation distinct from portable wire serialization.

## What it assumes from elsewhere

- [[elf64-structured-image]] owns the ELF schema and profile constraints.
- [[derive-binary-encoding]] owns optional instance synthesis from record fields.
