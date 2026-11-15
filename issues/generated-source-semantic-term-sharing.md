---
title: Preserve sharing in generated source-semantic endpoints
status: closed
labels: [compiler,elaboration,performance,proofs,codegen]
area: heather-in-heather
created: 2026-09-02
updated: 2026-10-24
---

The elaborated source-to-FunctionIR frontend needs equality endpoints for each
reflected source subtree. Named semantic functions make node-value proofs
compact, but the elaborator cannot reliably infer implicit equality endpoints
from recursively generated congruence calls. The current robust certificate
therefore emits one opaque expansion theorem per node with fully explicit
before/after operands.

This bounds kernel work per declaration and lets the 100-node source and x86
rails pass, but it repeats expanded source subtrees in theorem types and proof
arguments. At 100 nodes the source frontend is 7.46MB and the complete module
is 7.66MB. Rust reflection and generation take under 150ms each and parsing is
about 30ms, so formatting and parsing are not the performance problem. The
source frontend checks in 199.3s; the complete x86 artifact takes 677.7s.

## Desired direction

Extend the structured Heather emission boundary with a sink that can preserve
shared elaborated terms and expected-type relationships without constructing
unchecked kernel terms directly. Plausible experiments include:

- elaborator-facing expression DAG nodes with explicit sharing identities;
- named/opaque expected-type annotations restored without re-elaborating the
  expanded endpoint at every use; or
- a direct elaboration sink for `heather_emit` that retains ordinary name
  resolution and implicit insertion but interns repeated source expressions.

The trust boundary must remain unchanged: generated declarations still pass
through ordinary elaboration and kernel checking, and stale source bodies or
operand edges must remain rejectable. Success should reduce generated size to
roughly linear while materially lowering source-expansion and source-value
checking, not merely remove the sub-100ms text parse.

## Log

- 2026-09-11: Merged in [[generated-heather-direct-elaboration]] (2026-09-11): its question — is the render-to-source-then-parse round trip material — is answered by this issue's own 100-node datum (reflection/generation <150 ms each, parse ~30 ms, against 199.3 s checking). A direct sink stays listed here as one experiment, to be pursued only if that ratio changes.
- 2026-10-24: Not planned: what this issue is about was deleted in burn B2 (docs/native/native-program-logic-design.md §3.2). The verified `compile-x86` path (`function_ir_compile`, `compiled_returns`) replaces it; the last commit with the old code is `82521ea`.
