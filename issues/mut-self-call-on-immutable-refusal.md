---
title: Refuse a mut self call on a local that is not mutable, and lift the mut self return/annotation limits
status: closed
labels: [language,frontend,effects]
area: language
milestone: [nh-effects,lang-sequencing]
created: 2026-11-02
updated: 2026-11-02
---

A method-syntax call of a `mut self` method on a local that is not mutable,
`let p = y.m(a);` with a plain `let y`, elaborates to the `Mutated<T, R>`
record instead of being refused, so the error surfaces later, where `p` is
used as the answer (`docs/language/effects-capabilities-design.md` §2.2). The
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
in `Mutated` too; lifted 2026-11-02 by `issues/mut-self-early-return.md`).

## Log

- 2026-11-02: Built: a dot call of a `mut self` method that no statement threads is refused at the call ("nothing here keeps the update"; `refuse_unthreaded_mut_call` in crates/elab/src/dispatch/member.rs reads the callee's written result head, one surface lookup), with probes in linux_world_tests and imperative_statements_tests. An annotated `let p: T = x.m(a);` is now a candidate, split through a private `#mutcallN`. The `return` limit is [[mut-self-early-return]], built by #397.
