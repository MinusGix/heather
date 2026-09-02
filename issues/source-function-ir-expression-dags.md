---
title: Reflect pure source expression DAGs into FunctionIR
status: open
labels: [compiler,function-ir,metaprogramming,proofs,codegen]
created: 2026-09-01
updated: 2026-09-01
---

Grow the first source-to-FunctionIR frontend from one binary operation over
parameters to nested pure BitVec expressions. Assign stable ports in a
deterministic traversal, share repeated elaborated subterms when profitable,
and emit a staged source-denotation proof from the node equations rather than
asking conversion to normalize the complete expression at once.

The first additions should be constants and nested Add/Sub/AND/OR/XOR. This is
the source-side counterpart of the already-supported ALU backend and should
naturally produce the 20--100 node programs needed to measure real compiler
proof scaling. Surface `let` should lower into the same graph once expression
sharing is explicit; it should not require a sequential semantic IR.

## Acceptance

- Nested pure BitVec expressions generate deterministic stable-ID regions.
- Reused source values can become shared graph ports rather than duplicated
  computation.
- The denotation proof is staged by node and remains practical at 20 and 100
  nodes.
- Constants use the existing `Const` lowering and canonical `MOV r64,imm64`.
- Unsupported calls and effects decline at the source boundary with the
  operation or construct named.
- A stale node, operand edge, or source body is rejected by ordinary checking.
