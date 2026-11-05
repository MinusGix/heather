---
title: Name resolution allocates per lookup; elaborator clone grew 2.5x
status: open
labels: [frontend, elaboration, performance, modules]
area: language
created: 2026-08-05
updated: 2026-11-02
---

Filed off the modules implementing round's bench flag (2026-08-05,
[[modules]]) — recorded lever, one deliberate round when it matters, per
the accumulator discipline.

Two constant-factor costs the round measured and did not fix:

- **Per-lookup allocation.** `qkey` builds a `format!("{m}::{n}")`
  `String` and takes a second hash lookup on every name resolution
  (`crates/elab/src/names.rs`); `resolve_bare` allocates a `Vec` for
  listed-import filtering on every bare name. Measured: elab phase on
  constructor-heavy fixtures (`scale/wide-inductive:16/32`) at 1.48–1.55x
  the pre-modules baseline even in a quiet run.
- **Elaborator clone.** `corpus/prelude:clone` 119ns → 302ns (2.55x):
  `Elaborator` gained `NameIndex` and `module_scopes`, and the generated
  bench families clone a prelude'd elaborator per run.

Levers, if a round takes them: intern module names (a `u16` module id
ends both the `format!` and the string compares); key tables by
`(ModId, &str)` or a single pre-joined `Rc<str>`; make the listed-import
filter a per-scope precomputed map (`name → module`) built once at
`set_scope` instead of a `Vec` per lookup; `Rc` the tables that clone.

## When

Triggered: a frontend bench round where `scale/*` elab phase or the clone
row is the headline, or elab share of a real corpus file stops being
noise (it is ~1% of `ir_v1` today, which is why this is filed rather
than fixed).

## What it assumes from elsewhere

- **[[modules]]** owns the regime; nothing here may change observable
  resolution, only its cost.
- **[[frontend-benchmarks]]** owns the harness and baselines; the numbers
  above are against the 2026-08-04 baseline, pre-re-save.

## Log

- 2026-11-02: Related, filed 2026-11-02: [[layered-registry-lookups]]. Every registry miss scans one sealed layer per module (names, types, provenance, gendefs); names.rs is 3.5–4.7% of cold samples (docs/data-oriented-survey.md §6). Interning the keys, as this issue proposes, would make that scan cheaper but would not remove it.
- 2026-11-05: gardener: cites a file it shares with [[bounds-metadata-taxes-one-shot-checking]] (`docs/data-oriented-survey.md`); [[kernel-arena-terms-frozen-prefix]] (`docs/data-oriented-survey.md`).
