---
title: Compose reusable callee certificates across inputs and placements
status: closed
labels: [compiler,x86,proofs]
created: 2026-09-07
updated: 2026-09-08
---

## Scope

The first executable consumes a callee result contract, but its loaded execution
certificate still lists the leaf's instruction steps for the selected inputs.
Expose reusable function-level execution summaries parameterized over arguments,
permitted initial state, memory frame, and placement. Compose calls through those
summaries while continuing to check actual bytes and resolved references.

## Acceptance

- Separate a function's semantic/ABI contract from evidence that a placed byte
  fragment implements it. State entry/return, memory, and caller obligations.
- Parameterize beyond one closed input pair and absolute address. Specify the
  permitted relocations and connect each placed fragment's bytes to its checked
  implementation; moving code is not automatically semantics-preserving.
- Instantiate one checked callee interface at two call sites and demonstrate a
  permitted second placement without generating a fresh source/body proof for
  each occurrence. Retain kernel checking of the composed proof.
- Keep fetch, CALL/RET, memory-frame, and source-result connections explicit;
  a summary must not turn byte correctness into an unchecked producer promise.
- Reject wrong bytes/displacements, incompatible interfaces, unmet entry/frame
  premises, and use of a stale callee certificate after a relevant change.
- Record certificate structure and reuse for the example. Persistent caching
  and verifier resource-limit changes are not substitutes for composition.

## What it assumes from elsewhere

- [[x86-calls-stack-frames]] supplies concrete call execution.
- [[x86-call-memory-footprints]] owns memory/frame composition.
- [[named-abi-contracts]] owns convention identities and obligations.
- [[x86-symbolic-fragment-layout]] owns placement/relocation checks.
- [[runtime-compile-opt-in]] owns instance eligibility and artifact invalidation.

## Log

- 2026-09-07: Implemented a generic CallSummary/CallPremises boundary and fetched-trace composition. The producer emits a neutral-state source/contract summary once and uses it at two placements with distinct valuations, including explicit RSI preservation. Added a private-frame store to exercise memory effects. Focused generic checks pass; executable integration is being debugged under unchanged resource limits.

- 2026-09-08: The two-placement executable passes under unchanged 4 GiB / 300 CPU-second limits, exits 3 for inputs 21 and 1, and certifies the retained caller local, restored RSP, and dead private byte 22. One neutral-state source/ABI summary serves both instances; concrete successor, fetch, and access witnesses are connected by generic composition lemmas. Ordinary field layouts, register preservation, and file-byte observations use reusable lemmas to avoid repeated whole-state conversion. Details and validation controls are in `docs/x86-64-call-summaries.md`; final plain `scripts/test` passed: 2491 passed, 0 failed, 5 ignored. The new integration passed again in the full run (269.62 seconds reported). Issue and whitespace checks are clean. General frame allocation remains owned by [[x86-call-memory-footprints]], and broader relocation forms by [[x86-symbolic-fragment-layout]].
