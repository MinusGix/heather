---
title: A first piece of Heather written in Heather (candidate: the lexer)
status: closed
labels: [native,design]
area: heather-in-heather
milestone: [hih-self]
created: 2026-10-20
updated: 2026-10-31
---

Owns the roadmap's `hih-self` milestone (`docs/roadmap.md`): a first
component of Heather itself, written in Heather and compiled natively, so
that specific optimisations can be dogfooded on a real workload.

Candidate: the lexer, on the certified parser library (`lib/std/parser/`),
because its specification is small (the token grammar) and it reads input
the native stack already handles. Picking it needs:

1. A data representation for the token stream that native code can hold
   ([[datarepr-separation]]).
2. Heap allocation, or a proof that the lexer runs in a fixed buffer
   ([[memory-bound-certificates]]).
3. A way to compare it against the Rust lexer (differential tests are
   enough at first).

This waits on the program-logic and memory milestones; it is filed now so
those rounds know it is their customer.

## Log

- 2026-10-31: 2026-10-31: Split by docs/native/compiler-milestones-proposal.md §5 into [[self-hosted-lexer]] (milestone self-lexer: streaming tokens, no heap) and [[self-hosted-compiler]] (self-compiler). Its three needs have owners there: data representation and heap go to [[native-heap-arena]], and the differential test goes to the lexer round.
