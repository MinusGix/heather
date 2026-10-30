---
title: Narrow the early cutoff's registry and module-order refusals
status: open
labels: [tooling,caching,performance]
area: infrastructure
created: 2026-10-24
updated: 2026-10-30
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
- 2026-10-26: Root cause of the gate's cold cost found and fixed by giving every process one world (`docs/library-world-design.md`, `heather check --world lib`). Two causes. (1) `check` keyed every module of a closure with the *root's* lint profile, so a std module checked from `lib/native` or any `lib/_tests` folder had another image key than the same module checked from `lib/std/...`; the profile is now the module's own (`loader::Module::lint_profile`). (2) A module's image is keyed by everything its process loaded before it, and inductive tags count the inductives before them, so over a folder's own load order a shared module is a different elaboration, not a moved one; "the world's registries differ" was the refusal for nearly every module a folder had not built, and it is correct (filed [[nominal-tags-from-declaration-identity]]). The world is one order of the library's shared modules (greedy by folder, fewest new modules first); every gate child loads it up to the last one its folder needs, so each shared module has one key. Measured on a 4-CPU cloud box, release CLI, width one, the gate's folders one at a time over one fresh store, stale lane: cold 770 CPU-s on master, 496 with the world (in world order); the largest child (`lib/native`) 253 to 145, now only its own modules; warm 62 to 46 CPU-s (the world loads more modules than a folder's closure, but nothing re-elaborates). Also found: `native_cat.rs`'s `write-elf` and the suite's CLI image warmup ignored `HEATHER_SEMANTIC_IMAGES=accept-stale`, so after any compiler edit the stale lanes rebuilt cat's whole closure from source; that, not the certificate, is the "~470 s warm" (same-build warm `write-elf` of cat is about 17 CPU-s, cold about 250). Both now pass `--accept-stale-images` in those lanes. They stay off the world: its front is most of the library, and the warmup building it alone on a cold store went over the rail.
- 2026-10-30: Under closure keys ([[module-dag-build]]) the module-order refusal no longer arises between folders, and the registry digest is over the module's closure, not its whole prefix. Registry granularity inside the closure is still whole.
