---
title: Retire the Rust transcriber: freeze now, delete when the in-language path takes over v2
status: open
labels: [compiler,metaprogramming,design,meta]
created: 2026-08-11
updated: 2026-08-11
---

User direction (2026-08-11, post-transcriber-round review): get rid of the Rust transcriber to avoid having an oracle at all — dogfooding as methodology, forcing development in the language.

Staged, because the Rust path is currently the repo's ONLY cross-function generator: mul-via-add cannot move in-language until the opaque-globals kernel round lands (global references are neutral to elim^Trm, reduce.rs is_neutral_term). Deleting today deletes a capability, not just an oracle.

**Stage 1, in force now (the policy that carries the dogfooding pressure): the Rust walker is FROZEN.** New fragment features land in-language only; crates/elab/src/certgen.rs's Compiler is never extended, only kept passing. The oracle cross-check may stay while it is free.

**Stage 2, when opaque-globals lands and the in-language path serves cross-function calls: delete the Rust walker.** The shared emitters downstream of FnIr stay — they are not the oracle. What replaces the cross-check's role, already mostly in place: lib/certgen_code.hthr's own refl-theorems pin the transcriptions in-language; the positive fixtures make silent declines loud; the exactness fixtures catch different-but-converging output; the kernel judges the rest. Before deletion, confirm those four cover everything the byte-identical comparison currently pins (the layout interface especially — the file header's two-conventions block becomes the sole normative statement).

Related: certgen-transcriber-in-language-design sec. 5 (the oracle discipline being retired), [[certifying-generator]] (owner of the v2 path), [[generators-in-the-language]] (blockers 1-3).

## Log

- 2026-08-11: Stage 2's gate is OPEN (2026-08-11): the opaque-globals round landed cross-function transcription in-language -- mul-via-add byte-identical to the Rust v2 path (crates/elab/tests/certgen.rs::in_language_transcriber), callee markers + fn_body_code per docs/opaque-globals-analysis-design.md. Deleting the Rust walker is NOT done here: it still owes this issue's four-cover confirmation (the byte-identity oracle is what this round itself leaned on to land safely), and the deletion call is the coordinator/user's. Note one fixture edit while flipping mul to a positive: MUL's zero arm spells Zero so byte-identity tests the call, not seven's literal-spelling divergence.
