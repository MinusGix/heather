---
title: "Milestone: hand-written Compile instance checked end-to-end"
status: closed
labels: [milestone, compiler]
blocked-by: [kernel-v0-scope, ir-simulate-design, compile-typeclass-design]
created: 2026-07-22
updated: 2026-08-01
---

The moment the language's thesis is validated: one small pure function (e.g.
`add`), a hand-written `Compile` instance producing IR for it, and an `equiv`
proof checked by the Rust kernel. No generator required.

After this lands, the certifying generator ([[certifying-generator]]) is
"just" automation of what was done by hand.

## Log

- 2026-07-22: Kernel side is complete: substitutions, reduction, conversion, and now the ch. 04 type checker (typing.rs) all landed. Verifying a hand-elaborated term is: check_global_ctx -> check_local_ctx -> check_type -> check_term (see typing.rs module docs for presuppositions). Remaining blockers are compiler-side design ([[ir-simulate-design]], [[compile-typeclass-design]]). One elaboration constraint to respect: the box synthesis gap ([[box-synthesis-gap]]).
- 2026-07-23: kernel-v1-extensions filed for Id + fixed formers, but NOT added as a blocker: Leibniz Eq + Church-encoded toy IR are definable in the current grammar (see that issue), so the milestone can proceed on encodings.
- 2026-07-23: Route decision: frontend-first. The milestone deliberately moves behind [[elaborator-design]] + [[stress-proof-suite]]; [[ir-simulate-design]] will be worked in-language (IR as an inductive, simulate as a def) once the suite passes. Church-encoded toy version remains available as an early checkpoint if wanted, but is not planned.
- 2026-08-01: **Landed, and closing.** The milestone's sentence is true with no asterisk: `add` (as the theta-loop IR two LetCall wrappers deep), a hand-written instance `add_instance() -> CompileNat2(add_spec)` in lib/certgen/ir_v1.hthr producing prog/entry, and the certificate — Converges to the embedded spec result, ∀ arguments — checked by the kernel (release `heather check` 34.1s ok; elab test 2 passed under scripts/test). No generator, as specified. The instance shape is docs/archive/compile-typeclass-design.md (the design round and its acceptance both landed 2026-08-01); note the milestone did NOT need [[compile-typeclass-design]]'s class layer — that blocker's logical half (the certificate record) sufficed, and the operational half (resolution) was never a prerequisite of this issue's statement. [[certifying-generator]] is now 'just' automation of a value whose type exists.
