---
title: Model ELF flags and segment kinds with explicit wire values
status: open
labels: [compiler,elf]
area: heather-in-heather
created: 2026-09-07
updated: 2026-09-07
---

## Scope

Replace naked ELF flag and segment-kind constants with distinct typed values.
Keep ELF header machine flags separate from program-header permission flags
and from program-header kinds and OS extensions.

## Acceptance

- Give read/write/execute permissions explicit PF_R/PF_W/PF_X wire values and
  checked composition; never derive wire bits from host enum ordering.
- Model the supported program-header kinds, including LOAD and GNU_STACK,
  separately from permission masks and the ELF header's machine flags.
- State reserved/unknown-bit handling, distinguishing strict emission from any
  future permissive reader that preserves unknown bits.
- Preserve the current RX load and RW non-executable stack. Validate profile
  restrictions, including preventing accidental writable executable mappings.
- Check serialization laws and invalid combinations at the logical boundary.

## What it assumes from elsewhere

- [[elf64-structured-image]] owns header records and image serialization.
- [[x86-static-elf-executable]] owns the supported executable profile.
