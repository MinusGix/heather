---
title: Certify a reflected source fragment into FunctionIR
status: closed
labels: [compiler,function-ir,metaprogramming,proofs,codegen]
created: 2026-08-31
updated: 2026-09-01
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

The certified backend dependency is now satisfied. The recommended sequence is
to land [[function-ir-x86-commutative-reuse]] and
[[function-ir-x86-constants]] first, then reflect the already-supported pure
BitVec Add/Sub/AND/OR/XOR source fragment. That ordering is architectural, not
a hard dependency: the first add-only source theorem could begin sooner.

## Resolution

`function_ir_source` now reflects the first explicit fragment: two ordinary
`BitVec(64)` parameters and one Add/Sub/AND/OR/XOR application. It emits the
raw region, compact validity certificate, ordinary x86 lowering certificate,
source-denotation equality, and a `BlockArtifact` whose result is the actual
source call. The selected add path is the canonical `MOV RAX,RDI; ADD
RAX,RSI` byte sequence.

The negative control generates from addition and substitutes subtraction for
the source definition before checking; ordinary conversion rejects the stale
certificate. Unsupported nested expressions decline before lowering with a
specific fragment diagnostic. No theorem or data path mentions `ir_v1`.

The next source construct is nested pure expressions, tracked by
[[source-function-ir-expression-dags]].
