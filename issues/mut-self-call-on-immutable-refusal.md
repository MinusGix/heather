---
title: Refuse a mut self call on a local that is not mutable, and lift the mut self return/annotation limits
status: open
labels: [language,frontend,effects]
area: language
milestone: [nh-effects,lang-sequencing]
created: 2026-11-02
updated: 2026-11-02
---

A method-syntax call of a `mut self` method on a local that is not mutable,
`let p = y.m(a);` with a plain `let y`, elaborates to the `Mutated<T, R>`
record instead of being refused, so the error surfaces later, where `p` is
used as the answer (`docs/effects-capabilities-design.md` §2.2). The
sequencing design's refusal table (§10) wants it refused at the call: "call
it on a `let mut` local, or write `@M::m(…)` for the pair".

The parser cannot see that `m` is `mut self`, so the test is the
elaborator's: on the dot-call (`DotResolution::Method`) path, the target's
declared result is the prelude `Mutated` record and the call is not a
claimed `\0mutated` candidate. That path is hot, so the test must be cheap:
read the global's declared result head (no whnf of every inferred method
type). Done when the refusal is an `// expect-error:` probe in
`lib/_tests/std/os/linux/linux_world_tests.hthr`.

Also here: an annotated `let p: T = x.m(a);` is not a candidate (the
answer is annotated after the call), and `return` inside a `mut self`
body is refused (the `\0after` route would have to wrap the `Return` value
in `Mutated` too).
