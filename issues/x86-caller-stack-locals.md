---
title: Compile a caller with a live stack local across a call
status: open
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
