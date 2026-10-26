---
title: Narrow the early cutoff's registry and module-order refusals
status: open
labels: [tooling,caching,performance]
area: infrastructure
created: 2026-10-24
updated: 2026-10-26
---

The early cutoff (`docs/module-interface-cutoff-design.md`) moves a module's
image onto a changed dependency world when nothing it observed changed. What
it observes is coarser than what it reads in two places, and each costs a
whole downstream rebuild on an edit that should not need one.

- **Registries are observed whole.** Any registry event anywhere upstream (a
  new inductive, a designation, a derived instance) changes the registry
  digest of every later module, so adding one inductive to `nat` re-elaborates
  everything after it, exactly as before the cutoff. The name digest already
  shows the narrower shape: record what the elaboration asked the registries
  (which tags, which carriers, which designations), as the lookup record does
  for names, and digest only that.
- **Modules are found by name, in order.** A reference is found again in the
  module of the same name, and the registry digest is taken in load order, so
  a reordered or renamed closure refuses every move. That is the remaining
  acceptance of [[relocatable-semantic-module-images]] (reordered and
  unrelated-prefix worlds), and it matters once suffixes are built in
  parallel ([[parallel-checking-and-caching]]).

Neither is a soundness question: a refusal costs an elaboration. Measure
first which edits the library's history actually makes (a theorem or `fn`
appended moves everything; how often do edits add registry entries?).

## What it assumes from elsewhere

- **`docs/module-interface-cutoff-design.md`** owns the digests and the move.
  Assumed here: only that a refusal is always safe.

## Log

- 2026-10-26: Seen 2026-10-26 from the library gate (`crates/cli/tests/library.rs`), not from an edit. With one cache dir, a cold `heather check --expectations lib/std` followed by `check --accept-stale-images --expectations lib/native` re-elaborated most of the x86/Linux std prefix inside the lib/native process, about 150 CPU-s of its 350, and `check lib/std/arch` afterwards still kernel-checked 1124 declarations. A single-file check of `x86_64_asm.hthr` over the same store replayed all 25 modules. So images one folder's process writes are mostly refused by another folder's process, which loads the same modules in a different order, and every gate child pays its prefix cold. On a cold store that puts lib/native (std prefix plus function_ir plus the S3.2 compiler) over the 300 s rail. The suite's `cli_images_warmup` (scripts/test) works around this for native_cat.rs only, because write-elf's single-file closure has the same shape as the warmup's.
