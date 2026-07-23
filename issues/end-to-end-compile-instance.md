---
title: "Milestone: hand-written Compile instance checked end-to-end"
status: open
labels: [milestone, compiler]
blocked-by: [kernel-v0-scope, ir-simulate-design, compile-typeclass-design]
created: 2026-07-22
updated: 2026-07-23
---

The moment the language's thesis is validated: one small pure function (e.g.
`add`), a hand-written `Compile` instance producing IR for it, and an `equiv`
proof checked by the Rust kernel. No generator required.

After this lands, the certifying generator ([[certifying-generator]]) is
"just" automation of what was done by hand.

## Log

- 2026-07-22: Kernel side is complete: substitutions, reduction, conversion, and now the ch. 04 type checker (typing.rs) all landed. Verifying a hand-elaborated term is: check_global_ctx -> check_local_ctx -> check_type -> check_term (see typing.rs module docs for presuppositions). Remaining blockers are compiler-side design ([[ir-simulate-design]], [[compile-typeclass-design]]). One elaboration constraint to respect: the box synthesis gap ([[box-synthesis-gap]]).
- 2026-07-23: kernel-v1-extensions filed for Id + fixed formers, but NOT added as a blocker: Leibniz Eq + Church-encoded toy IR are definable in the current grammar (see that issue), so the milestone can proceed on encodings.
