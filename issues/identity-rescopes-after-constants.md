---
title: Delete the elaborator's rescopes and rescope memos that constants made the identity
status: open
labels: [kernel,elaborator,simplicity,cleanup]
area: kernel
created: 2026-11-10
updated: 2026-11-10
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
