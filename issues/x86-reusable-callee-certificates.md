---
title: Compose reusable callee certificates across inputs and placements
status: open
labels: [compiler,x86,proofs]
created: 2026-09-07
updated: 2026-09-07
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
