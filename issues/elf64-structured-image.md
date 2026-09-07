---
title: Represent ELF64 headers and images with structured records
status: open
labels: [compiler,elf]
created: 2026-09-07
updated: 2026-09-07
---

## Scope

Replace the large literal header array in `lib/elf64.hthr` with explicit ELF
header, program-header, and image records plus wire encoders. Keep the restricted
static executable profile and its exact emitted-byte certificate.

## Acceptance

- Express field widths, ordering, little-endian encoding, wire sizes, offsets,
  and alignment explicitly. Host-language record layout is not the wire format.
- Make the producer and logical model use structured fields, while continuing
  to certify the actual serialized bytes before publication.
- Preserve the current executable bytes and behavior for the existing example;
  retain malformed-header negative controls and size/entry constraints.
- Document which ELF features remain unsupported. No section table or object-file
  pipeline is required merely to make the representation structured.

## What it assumes from elsewhere

- [[x86-static-elf-executable]] owns the initial supported ELF profile.
- [[elf64-typed-flags]] owns typed flags and their wire values.
- [[binary-encoding-trait]] owns reusable wire-encoding contracts. Explicit
  per-record encoders can land first; this refactor must not wait for generic
  metaprogram synthesis in [[derive-binary-encoding]].
