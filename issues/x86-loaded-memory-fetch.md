---
title: Connect loaded ELF memory to canonical x86 instruction fetch
status: closed
labels: [compiler,x86,memory,proofs]
created: 2026-09-07
updated: 2026-09-07
---

## Scope

Own the bridge from the restricted ELF image to a byte-addressed loaded memory
and from bytes at RIP to the existing canonical decoder and execution relation.
The completed bridge connects the restricted image certificate to fetched
canonical execution and the existing source-result certificate.

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


- 2026-09-07: Completed the restricted loaded-image implementation. `elf64_load`
  supplies absolute-address reads and execute permission for the file-backed RX
  view; `x86_64_fetch_block` composes canonical fetched steps; `linux_x86_64_fetch`
  links the terminal fetched syscall bytes to the source-result exit request.
  The generated trace fixes memory/RIP from the actual checked ELF file and keeps
  initial GPRs/flags arbitrary. No loader or syscall implementation is assumed
  inside the kernel. The first profile has no zero-fill tail or writable data.
- 2026-09-07: Certificates use structural per-byte witnesses, with a general
  theorem relating them to the executable fetch function. Binary address
  literals, individual read/permission/advancement facts, flattened states,
  and per-step equality to the original source-certified state sequence keep
  checking within the existing fuel and memory rails. No limits were raised.
  Native integration passed for exit 27 and full result 505 reported as 249.
  Header, mapping, payload, and state-advancement refusal checks cover the new
  boundary. Calls/frames remain owned by [[x86-calls-stack-frames]], layout by
  [[x86-symbolic-fragment-layout]], and structured headers by [[elf64-structured-image]].
- 2026-09-07: Final validation: HEATHER_TEST_JOBS=3 scripts/test passed (2470 passed, 0 failed, 5 ignored; 426s runner wall time). Focused x86 and mapping/refusal rails passed. The persistent target/x86-native/mix-loaded executable is 233 bytes, exits 27, and carries the loaded-trace certificate. No checker limits were raised; temporary diagnostics were removed.
