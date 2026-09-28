---
title: Method chains re-infer each receiver once per level: 2^depth elaboration
status: closed
labels: [frontend,elaboration,performance]
created: 2026-09-24
updated: 2026-09-28
---

A method call infers its receiver in `member_head` to find the owner, and the
desugared application then elaborates the same receiver again. In a chain
`a.f().g().h()` each level re-infers everything below it, so elaboration is
2^depth in the chain length. That holds for inferable chains (before the
namespace round) and, on the failure path, for uninferable ones (after it).
Library chains are at most three calls deep, so this is recorded rather than
urgent. The lever, if a client grows long chains: hand the inferred receiver
term to the desugared call instead of the surface expression. Found by the
namespace round (docs/receiver-member-resolution-design.md).

## Log

- 2026-09-28: Fixed receiver reinference with a dot-call-scoped cache shared by resolution, the desugared argument, and checking retries of every nested prefix. Both successful terms/types/levels and failed inference outcomes are reused. An expected checking type still gets its own retry after failed inference; successful reuse records the normal mismatch candidate for the kernel gate.

  The cache registers only dot receivers, keyed by their source spans, so desugared applications cannot collide with its keys. It is bounded to the enclosing call's context, checks the local context and alias identities, and is discarded on binder pushes, context prefixes, and quotation rescoping. Ordinary non-chain dot calls take the borrowed-context path. Receivers containing free argument slots retain their speculative checking path.

  Regression tests count one inference per nested prefix for inferable and failing chains, including neutral and literal receivers, a checking-only width, named argument permutations, an open element type, and an incompatible-result refusal. Context unit tests cover shared retries and scope invalidation. The new timings columns are `dot_receiver_inferences` and `dot_receiver_reuses`. This removes the exponential reinference; source cloning and the existing telescope/type traversals still have their own costs.

  Verification: focused type-member tests passed (38), context unit tests passed (3), and the full `scripts/test` passed (3,074 passed, 0 failed, 5 ignored). `scripts/perf ab`, three interleaved samples over neutral chains of depth 8, 12, and 14, confirmed 31 receiver inferences and 31 reuses, with `unify_calls` dropping from 20,733 to 34 and `shift_global_nodes` from 1,224,440 to 4,590. The 29 existing unchanged columns included kernel checking and conversion counters. The harness warned about host load, so no time delta is claimed. The report and raw timings remain under `target/perf-ab/`.
