---
title: The elaborator accepts a field of a theorem-built record as if the theorem unfolded; the kernel then refuses with an unlocated NotConvertible
status: closed
labels: [elaboration,kernel,diagnostics]
created: 2026-09-24
updated: 2026-09-24
---

Found 2026-09-24 while hand-writing the bounded-loop glue
(`docs/native-bounded-loops-design.md` §6).

Shape: `let read = X_read_artifact(...)` binds a `ReadThenArtifact` built by a
*theorem*, and the proof then uses `read.memory_preserved` (type
`read.continuation.after.memory = s1.memory`) and `read.registers_preserved`
where `X_body_after(byte_load_after(...))` was expected. That equality needs
`read.continuation.after` to reduce, which needs the theorem to unfold.
Theorems are opaque (`crates/elab/src/lib.rs`, see
`docs/decreases-unfolding-design.md`), so it should not reduce.

The elaborator accepted the declaration. The kernel gate then rejected it as
`the kernel rejected <decl>: NotConvertible`, located at the declaration
header with no sub-term. It took a bisection by hand, one theorem per let
value, to find the cause.

Reproduction: `crates/elab/tests/function_ir_loop_trace.rs` generates the
search loop. In `loop_native.rs`'s `body_step`, replacing
`{st}_body_memory(loaded)` in the `memory` chain with
`X_read_artifact(<observed args>).memory_preserved` reproduces it.

Two questions. Which elaborator path treats the theorem as transparent
here (a let-bound value's type, or the record projection's reduction)? And
could a kernel NotConvertible at least name the first mismatching
sub-terms? The kernel is the gate, so this is not a soundness problem, but
the diagnostic cost an hour.

## Log

- 2026-09-24: Second instance, 2026-09-24 (slice C). The elaborator accepted `match r { Continue(p) => word_of_nat(64, p), Break(p) => word_of_nat(64, p) }` where `word_of_nat(64, loop_step_payload(r))` was expected, for a neutral `r` (a commuting conversion). The kernel refused it, unlocated. The same symptom might have a different cause, since no theorem is involved here. So the question is broader: which elaborator conversion rules does the kernel lack?
- 2026-09-24: Audit done. The title's premise was wrong: the elaborator has no conversion rule of its own. It records inferred/expected pairs and the kernel judges (`note_check_mismatch`, lib.rs); every conversion it does run goes through kernel conversion over a Ψ where theorems have no body. Both instances were diagnostic gaps. (1) The `.f` checking arm returned four paths (bare projection, and the three `apply_implicit`/`apply_projection` results) without recording the pair; they record now. (2) The commuting-conversion case was recorded and decided `NotConvertible`, then dropped because a `match` does not spell ("readable or silent"). A decided mismatch that does not spell now keeps the gate's verdict and moves its span to the site, as a `refl` note does (`MismatchNote::Located`). Precedence: a note spelling both types, then a `refl` note, then a located-only note (the full suite's two wrong-unit controls caught the other order). Tests: `check_reports_mismatch.rs` (three new). The kernel-side sub-term report is residue for terms with no checking site: [[kernel-refusal-without-a-checking-site]].
