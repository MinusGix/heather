---
title: Compile a caller with a live stack local across a call
status: closed
labels: [compiler,x86,proofs]
created: 2026-09-07
updated: 2026-09-07
---

## Scope

Extend the forwarding-only source slice to a caller that computes a value,
saves it in a concrete frame slot, calls a leaf, reloads the value, and combines
it with the returned result. Start with one fixed-width local and direct calls.
A conservative frame strategy is sufficient; general register allocation and
arbitrary call graphs are not required for this milestone.

## Acceptance

- Add or reuse canonical stack load/store forms with exact bytes, byte-memory
  access premises, and fetched execution through the same machine state.
- Lower source computation before and after a call, with a real saved/reloaded
  frame value. Preserve source-definition/result coupling and explicit callee
  eligibility; reject unsupported source/frame shapes clearly.
- Reserve and release the slot, maintain call alignment, prove capacity and
  disjointness from both return slots and child frames, and restore final RSP.
- Consume the callee's clobber/memory contract so the caller proof does not
  accidentally depend on scratch registers retaining values.
- Build and run a standalone ELF whose result depends on both the returned
  value and the recovered local. Reject wrong slot offsets, protected-slot
  writes, missing frame restoration, and unsupported frame shapes.
- Document the bounded convention/profile and leave recursion, arbitrary
  spills, address escaping, and general call-graph lowering to later owners.

## What it assumes from elsewhere

- [[x86-call-memory-footprints]] owns the frame contract.
- [[named-abi-contracts]] owns reusable convention vocabulary.
- [[x86-calls-stack-frames]] supplies the working forwarding-call baseline.
- [[x86-symbolic-fragment-layout]] owns placement and symbolic references.
- [[runtime-compile-opt-in]] owns Compile eligibility; this milestone must not
  silently broaden automatic compilation of unmarked callees.

## Log

- 2026-09-07: Implemented the bounded leaf(left,right) XOR (left XOR right) source customer. A 341-byte standalone ELF saves the XOR in [RSP], calls a leaf that clears R11, reloads through the callee memory-effect contract, and exits with source result 40 for inputs 20 and 22. The dedicated integration test passes in 268.54 seconds under ordinary limits. Full regression validation is running.
- 2026-09-07: The first full run passed the live-local integration (293.83s) but failed the forwarding-call build at its resource limit; the isolated forwarding rerun passed (260.04s). Fetch generation now shares named concrete addresses across premises to avoid repeating dependent vector checks. Both executable cases are being revalidated before the final full run.
- 2026-09-07: After sharing concrete fetch-address declarations, both native integration targets pass under the standard limits: forwarding 250.59s and live stack local 229.25s. The final full regression run is in progress.
- 2026-09-07: The second parallel full run passed forwarding but killed the live-local build at 302.33s (SIGKILL), despite its 229.25s focused pass. Extended literal sharing from fetch addresses to all concrete words in the call certificate. A per-certificate pool emits each transparent checked vector once; structured Module composition places these declarations before the trace. Full validation is running with the original limits and parallelism.
- 2026-09-07: Found a cold-cache harness gap: native SemanticSession images use the elaborator-source fingerprint, but scripts/test warmed only the elaborator test caches. Added a bounded native prefix warmup using the existing encoder/corruption test, following the existing semantic warmup policy; exact-build image replay still kernel-checks declarations. The next full validation will start with a fresh native cache.
- 2026-09-07: Final plain full suite passed from a fresh native cache: 2,490 passed, 0 failed, 5 ignored (662s total). Native prefix warmup passed in 26.32s; forwarding integration passed in 219.79s and live-local integration in 257.02s under unchanged 4 GiB / 300 CPU-second limits. The bounded milestone is complete. General frame allocation/extent/aliasing remains owned by [[x86-call-memory-footprints]], named ABI coverage by [[named-abi-contracts]], and reusable summaries by [[x86-reusable-callee-certificates]].
