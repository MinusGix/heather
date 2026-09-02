---
title: Measure a direct elaborator sink for generated Heather
status: open
labels: [compiler,elaborator,metaprogramming,performance]
created: 2026-09-02
updated: 2026-09-02
---

`heather_emit` currently renders its construction IR to source, then uses the
ordinary parser and elaborator. Measure how much time and allocation parsing
that generated source contributes at 20- and 100-node FunctionIR artifacts.

If material, prototype an alternate sink from the same `Expr`/`Declaration`
values into elaborator input data. It must retain ordinary name resolution,
implicit insertion, metadata lookup, diagnostics, and independent kernel
checking. Direct kernel-term construction is out of scope: that would move
elaboration responsibility into compiler generators and enlarge the trusted
semantic surface.

## Acceptance

- Profiles separate rendering, parsing, elaboration, and kernel checking.
- A direct sink is pursued only if rendering/parsing is a meaningful fraction
  of total cost.
- Text and direct sinks elaborate to byte-identical kernel terms on a focused
  generated-module corpus.
- Compiler clients construct only the shared emission IR and do not depend on
  sink-specific details.
