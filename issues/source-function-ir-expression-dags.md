---
title: Reflect pure source expression DAGs into FunctionIR
status: open
labels: [compiler,function-ir,metaprogramming,proofs,codegen]
area: heather-in-heather
milestone: [hih-passes]
created: 2026-09-01
updated: 2026-10-24
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

## Progress

The elaborated-body frontend now recognizes resolved Add/Sub/AND/OR/XOR and
closed `bitvec::ofNat(64, literal)` applications. It assigns stable IDs by
deterministic postorder and structurally memoizes expressions. The checked
acceptance function deliberately uses a surface `let`; although elaboration
substitutes its body, reflection recovers one shared Add port. Its four nodes
are shared Add, Const 7, dependent Add, and final XOR.

Generated source semantics use named node-list suffixes, one opaque value
theorem per node, one small semantic function per port, and per-node expansion
equalities. Operation-specific congruence lemmas keep each expansion proof one
layer deep without relying on the elaborator to infer endpoints from recursive
proof arguments.

The parameterized rail now passes at both requested scales. The source-only
frontend checks in 20.9s at 20 nodes and 199.3s at 100 nodes. The complete x86
artifacts check in 105.6s and 677.7s respectively. At 100 nodes reflection and
generation remain below 150ms each; proof elaboration and checking dominate.
The detailed breakdown is recorded in `docs/native/function-ir-design.md`.

The expanded endpoint syntax is still 7.46MB at 100 nodes; follow-up is tracked
in [[generated-source-semantic-term-sharing]]. Remaining acceptance work here
is a focused kernel negative control for a stale internal operand edge.
Unsupported-call decline, repeated-reflection determinism, constants, sharing,
and the 20/100-node source-to-x86 path are covered.

## Log

- 2026-10-24: B2 (2026-10-24): the staged source-denotation publication is deleted; the reflector is `function_ir_source/program.rs` and agreement is one `refl` equation per function (see [[function-ir-source-denotation-after-b2]]).
