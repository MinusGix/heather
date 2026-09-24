---
title: Method chains re-infer each receiver once per level: 2^depth elaboration
status: open
labels: [frontend,elaboration,performance]
created: 2026-09-24
updated: 2026-09-24
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
