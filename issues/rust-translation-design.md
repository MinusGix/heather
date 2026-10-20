---
title: Design the Rust-to-Heather translation: subset, semantics source, target
status: open
labels: [translation,semantics,design,research]
area: rust-in-heather
milestone: [rust-design]
created: 2026-10-20
updated: 2026-10-20
---

Owns the roadmap's `rust-design` milestone (`docs/roadmap.md`): translate
Rust code into Heather to prove properties about it. The design note should
settle:

1. The subset first: safe Rust without trait objects or interior
   mutability, say, and how it grows.
2. The semantics source: MIR, as in functional translations such as Aeneas
   (Rust to Lean), or the surface language.
3. What the translation targets: a functional model where borrows become
   values, or a program logic over a memory model. Either way it depends on
   the memory work ([[memory-bound-certificates]],
   [[byte-memory-access-model]]) and on interaction trees for I/O
   ([[interaction-trees-container-model]]).

No implementation until those dependencies have a shape.
