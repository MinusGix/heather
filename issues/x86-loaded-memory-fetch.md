---
title: Connect loaded ELF memory to canonical x86 instruction fetch
status: open
labels: [compiler,x86,memory,proofs]
created: 2026-09-07
updated: 2026-09-07
---

## Scope

Own the bridge from the restricted ELF image to a byte-addressed loaded memory
and from bytes at RIP to the existing canonical decoder and execution relation.
The current image certificate proves serialization and typed execution; it does
not yet connect those two through loaded memory and fetch.

## Acceptance

- Specify PT_LOAD placement, file-backed bytes, zero-fill where supported, access
  permissions, entry address, bounds, and address overflow without assuming wrap
  is harmless. State the supported loader profile explicitly.
- Prove that the emitted image's entry and code bytes inhabit their specified
  virtual addresses, and that fetching there produces the certified instructions.
- Feed the existing decoder/execution relation; distinguish failed memory access,
  unsupported decoding, and architectural faults rather than making another
  independent x86 semantics.
- Reject damaged payloads, mismatched mappings, non-executable entry addresses,
  and out-of-range fetches in meaningful negative controls.
- State Linux loading and syscall delivery assumptions separately. This bridge
  does not claim to verify the Linux kernel.

## What it assumes from elsewhere

- [[byte-memory-access-model]] owns byte-store and access-policy semantics.
- [[x86-64-machine-model]] owns canonical decoding and execution.
- [[x86-static-elf-executable]] supplies the initial image and entry certificate.


## Log

- 2026-09-07: First slice implemented in `lib/std/arch/x86_64/fetch.hthr`:
  explicit byte-reader/execute-policy interface, exact-span fetch outcomes,
  nonwrapping address advancement, and `ExecuteFetched` connecting the same
  before-state memory to canonical `ExecuteAt`. Focused x86 checks pass,
  including neutral/open inputs and negative controls. ELF placement and
  whole-program fetched execution remain open; no loader proof is claimed.

- 2026-09-07: Full validation: `HEATHER_TEST_JOBS=3 scripts/test` passed
  (2469 passed, 0 failed, 5 ignored; runner wall time 428s). The focused x86
  target also passed independently. Issue and whitespace checks are clean.
