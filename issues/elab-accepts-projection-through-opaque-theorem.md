---
title: The elaborator accepts a field of a theorem-built record as if the theorem unfolded; the kernel then refuses with an unlocated NotConvertible
status: open
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
