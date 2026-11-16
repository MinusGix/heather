---
title: Delete the elaborator's rescopes and rescope memos that constants made the identity
status: open
labels: [kernel,elaborator,simplicity,cleanup]
area: kernel
created: 2026-11-10
updated: 2026-11-16
---

[[psi-references-by-level]] made committed definitions **constants**, named
from the start of Ψ: `shift_global` and `apply_global` are the identity on
them, and a term closed in Ψ's variables is one spelling in every extension
of Ψ. The elaborator still carries the machinery it needed when a reference
counted from the end of Ψ. None of it is wrong, and all of it is now the
identity on what it is applied to, so it can go.

## What to delete or narrow

1. **Rescopes of committed things.** The `shift_global(now - at)` sites
   applied to a statement, a body or a lowering read out of Ψ or a registry
   (`resolve_at`, `body_of`, `unfold_gen_app`, `read_now`, `named_type`'s hit
   path, `lift_proved`). Each is an identity walk the global bound skips at
   the root; deleting the call also deletes the `at` it needed.
2. **Rescope-on-read memos.** `guard_reads`, `guard_spine_reads`,
   `guard_slot_formers` and `ty_code_fn_at`'s template shift exist to pay a
   rescope once per Ψ length. With nothing to rescope they are a lookup that
   returns its key.
3. **Scope arithmetic in reference construction.** `gen_ref_len`,
   `lowering_scope`, and the `global_padding`/`meta_offset` terms that enter
   a committed reference's index. They still matter for **variables** (goals,
   metas, `meta fn` binders); the audit is which callers only ever build a
   constant.
4. **Memo keys that include a Ψ length.** `InstanceMatchKey::scope`,
   the character literal memo's scope, `ScopeMemo::psi`: a key component
   that changes at every commit when the answer is closed in the variables.
   `named_type`'s guard already widened by itself (the 2026-11-10 log of
   [[psi-references-by-level]]); these have to be read one at a time,
   because some answers depend on what is in scope (instances, dictionaries)
   and not only on the spelling.
5. **`shift_univ_psi`** rebuilds all of Ψ under a universe binder. Σ could
   be left alone if a committed binding is required closed in universe
   variables too, which needs its own adequacy sentence in
   `crates/kernel/DESIGN.md`.

## Shape of the work

Items 1 to 3 are refactors with identical `--timings` count columns as the
acceptance test (`scripts/timings --diff`). Item 4 moves counters and wants
a `scripts/perf ab`. Item 5 is a kernel change.

## Log

- 2026-11-10: First part, items 1 and 2. Deleted from the elaborator: the guard scope table (`guard_at`, `GuardKey`, `guard_ty`, `guard_slots`, `guard_read`, `read_now`, `SpineCodes::read`) and the three memos that paid its rescopes once per Ψ length (`guard_reads`, `guard_slot_formers`, `guard_spine_reads`); `ty_code_fn_at`/`ty_code_fn_now`, now one `ty_code_fn_entry` that returns the entry as stored; the after-push rescopes in `register_rec_projs`, `register_m_sig`, `register_iwf_sig`, `register_wf_slots` and `unfold_gen_app`; `named_type`'s hit path; the derived table's `shift_global(now - d.at)` at its four readers, `weaken_global_below`, and the Ψ length the pending queue carried; and the rescopes of a committed statement or body in `fn_type_code_at`, `conclusion_clashes`, `numeral_templates`, `operand_carrier` and `wf_slot_refs`. About 500 lines out and 165 in. The table was already dead: `mentions_global` asked whether a shift moves a copy, no copy that names committed definitions is moved, so nothing was ever inserted. What each deletion rests on is one fact, that `GlobalCtx::commit` refuses under a global variable, so anything alive across a commit names constants only; the registry commits and the mint of a queued derivation assert it in debug builds. `scripts/perf ab --base HEAD` on the showcase: 42 count columns identical across both binaries and every sample, `shift_global_nodes` about 445 k → 250 k (a counter that already differs between two runs of one binary), seconds unchanged, as expected of calls the global bound skipped at the root. `scripts/test --pr`: 3022 passed, 0 failed.

  Left for a second part, because it changes the image format: the `at` fields of the four guard-copy events and of `DerivedInst` are still written, relocated and hashed (`module_relocate.rs`'s `scope`, `WorldHasher::ty(scope, …)`, `shape_positions`), and nothing reads them any more. `MetaDef::psi_len` is not the same case: `lib.rs` compares it with the Ψ length to recognise a definition registered at this position. Items 3 to 5 are untouched.
- 2026-11-16: Second part (branch claude/project-thread-r29qkd, 2026-11-16):
  - The dead `at` fields are gone. They were on the four guard-copy events and on `DerivedInst`. Relocation now moves those payloads through a reindex that accepts constants only and refuses a free global variable. The projection hashes them at no particular scope. Debug builds assert at commit that all five kinds of payload are closed. The image and interface formats are bumped.
  - Item 3, for the recognizers: `gen_def_of` answers `None` for a global variable, because a generated definition is committed and so referenced as a constant. With that, `gen_ref_len`, `code_key_at`, `gen_app_of_at`, `unspell_deep_now`, the scratch width of `unspell_here_in` (now `unspell_ref` behind `unspell_here`) and the `len_at` anchor of `unspell_ty_deep` all go. Before deleting, I checked the claim with a whole-library run of plain `scripts/test`, with a tripwire that panicked if a variable resolved to a generated definition. It never fired: 4051 passed, and the one failure was a native certificate killed at the rail under contention, which passes when run alone.
  - Item 1, two more sites: the `shift_global` of committed statements in `dispatch/member.rs` and `dispatch/receiver.rs`.
  - `scripts/test --pr`: 3074 passed, 0 failed.
  - Still open: item 3's display and reference inversions, which are right to keep the Ψ length because a variable can be a goal (`global_abs_of`, `lowering_scope`'s other readers); item 4 (memo keys carrying a Ψ length, which wants `scripts/perf ab`); item 5 (`shift_univ_psi`, a kernel change).
- 2026-11-16: Item 4 (2026-11-16):
  - Four of the declaration-attempt memos keyed on `lowering_scope` (the signature plus the goal padding and the `meta fn` padding): `children_annotations`, `wf_slot_annotations`, `instance_matches` and `char_literals`. They now key on the signature's length, as `emitted_cx` already did. Their answers name generated definitions as constants, so the padding cannot change them. A registration mid-attempt can change them, and it grows the signature.
  - `ScopeMemo` keeps both its signature length and its `pad`. Its answers are dictionaries elaborated in scope, and those can depend on what the signature holds and on the goals.
  - `scripts/perf ab` on `calc_parser`, `x86_64_asm_runs` and `function_ir_spills_tests`: all 45 counter columns are identical, and the seconds are within the noise. On these files the padding never varied while one of these memos was live, so this change is about the keys stating what the answers depend on, not about speed.
  - Plain `scripts/test`, with #697 (the master fix) merged in locally: 4057 passed, 1 failed. The failure was `native_linked`'s certificate killed at the rail under contention; it passes when run alone.
  - Item 5 (`shift_univ_psi`) is left; it is a kernel change.
