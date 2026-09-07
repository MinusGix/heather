---
title: Build a standalone ELF64 executable from certified x86 code
status: closed
labels: [compiler,x86,elf,proofs,cli]
created: 2026-09-07
updated: 2026-09-07
---



## Scope

First direct-executable milestone after [[x86-native-export]]: generate a
small Linux x86-64 ET_EXEC image, initialize the two source inputs, run the
certified body inline, and request Linux exit with its result. No assembler,
external linker, manual wrapper, or RET participates.

## Acceptance

- A Heather specification fixes the restricted ELF profile and its byte,
  size, entry-offset, and permission constraints.
- The actual emitted header and payload are checked before publication.
- Canonical typed execution proves input initialization and exit setup;
  a constructed graph witness connects the body result to the source call.
- Native integration runs with no toolchain on PATH and checks exit status,
  including low-byte truncation. Header mutation controls fail in the kernel.
- OS loading, physical fetch, and syscall delivery remain explicitly stated
  assumptions; no claim of a verified Linux kernel or complete x86 machine.

## Ownership and sequencing

- [[x86-native-export]] owns the shared source-to-body certificate path.
- [[byte-memory-access-model]] and [[x86-64-machine-model]] own the memory and
  architectural execution groundwork for the next loaded-image/fetch bridge.
- [[bitvec-ofnat-large-literals]] owns the current large-literal limitation.
- Calls/stack frames and memory-backed output follow this first image slice.

The profile, proof boundaries, source references, and invocation are in
`docs/x86-64-static-elf.md` and `examples/x86-native/README.md`.

## Log

- 2026-09-07: Implemented build-x86, the restricted StaticElf64Image specification, concrete entry valuations, LinuxInlineTrace/exit-request certificates, and exact serialized-header/payload checks. The 233-byte standalone mix executable exits with 27; native integration builds with no toolchain on PATH and also checks 505 truncated to exit status 249. All 27 header mutations are kernel-rejected. Full verification via HEATHER_TEST_JOBS=3 scripts/test: 2469 passed, 0 failed, 5 ignored; issue and diff checks clean. Loader/fetch/syscall assumptions and the subsequent memory/call milestones remain explicit in docs/x86-64-static-elf.md.

## Follow-up owners

- [[x86-loaded-memory-fetch]] — Connect loaded ELF memory to canonical x86 instruction fetch.
- [[x86-calls-stack-frames]] — Certify x86 calls and concrete stack frames.
- [[elf64-structured-image]] — Represent ELF64 headers and images with structured records.
- [[binary-encoding-trait]] — Define reusable explicit binary wire-encoding contracts.
- [[derive-binary-encoding]] — Synthesize binary encoders from record field instances.
- [[elf64-typed-flags]] — Model ELF flags and segment kinds with explicit wire values.
- [[runtime-compile-opt-in]] — Require explicit Compile instances or runtime derivation markers.
- [[runtime-extern-c-abi]] — Define explicit C ABI imports and runtime exports.
- [[x86-symbolic-fragment-layout]] — Lay out certified code fragments and resolve symbolic references.
