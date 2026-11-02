---
title: Allow return inside a mut self method body
status: open
labels: [language,frontend,effects]
area: language
milestone: [nh-effects,lang-sequencing]
created: 2026-11-02
updated: 2026-11-02
---

`return` inside a `mut self` method body is refused at parse time
(`crates/syntax/src/parser.rs`, "`return` is not supported in a `mut self`
method yet"; docs/effects-capabilities-design.md §2.1). The method's result
is `Mutated(x, value)`, built at the body's end, and an early exit's
`\0after` route leaves with `ForStep::Return(e)`'s value alone, so the
receiver as it stood at the `return` would be lost.

Lifting it: the returning route wraps its value as `Mutated(x, e)` with the
receiver read at the exit. Inside a loop the receiver is loop state, so the
`Return` leaf has to carry the state beside `e` (or the loop's exit reads
`x` from the state it returned with), which is the part that is more than a
wrap. Done when a `mut self` method with an early `return`, in and outside a
loop, checks in `lib/_tests/std/core/imperative_statements_tests.hthr`
against its hand-written `Mutated` reading by `refl`, at a literal and a
neutral receiver.

Split from mut-self-call-on-immutable-refusal, whose refusal and annotated
`let` parts are built.
