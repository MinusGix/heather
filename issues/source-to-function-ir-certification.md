---
title: Certify a reflected source fragment into FunctionIR
status: open
labels: [compiler,function-ir,metaprogramming,proofs,codegen]
blocked-by: [function-ir-x86-lowering-generator]
created: 2026-08-31
updated: 2026-08-31
---

The new FunctionIR currently begins from a concrete compiler-owned graph.
Build the first source-function frontend for it: reflect a deliberately small
pure BitVec fragment, construct FunctionIR, emit `RegionValid`, and prove the
graph denotes the original function. Compose that certificate with generated
x86 lowering for the first end-to-end source-to-bytes theorem on the new path.

This should displace overlapping `ir_v1` compilation rather than wrap or
translate through its constructor-tree representation. The first fragment may
be narrow, but its decline boundary must be explicit and its certificate must
name the source function actually reflected.

## Acceptance

- A source-level BitVec add function reaches canonical x86 bytes through
  generated FunctionIR and lowering certificates.
- A stale or dishonest reflected body is rejected by the ordinary checker.
- Unsupported source syntax declines with a useful reason.
- No correctness theorem factors through `ir_v1` merely for compatibility.
- The result identifies the next source construct needed to retire a concrete
  remaining `ir_v1` customer.

## What it assumes from elsewhere

- **[[function-ir-x86-lowering-generator]]** supplies the certified backend.
- **[[compile-typeclass-design]]** owns how the completed source-to-code
  certificate is packaged for compiler discovery.

