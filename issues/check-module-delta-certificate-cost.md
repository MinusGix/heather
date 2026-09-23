---
title: check_module_delta makes a generated certificate's statements ~25× slower than elab_module_source
status: open
labels: [performance,elaboration,cache,x86]
created: 2026-09-23
updated: 2026-09-23
---

Found 2026-09-23 while trying to give `build-x86`'s generated certificate module the semantic-image cache the bundled library already has (so a repeated build replays instead of re-elaborating).

Routing the certificate through `SemanticSession::check` (crates/cli/src/semantic.rs) made **image hits** nearly free — a repeated `build-x86` of `examples/x86-native/stack_save.hthr` at the same inputs went 23 s → 1–2 s — but made **misses** far slower, because a miss elaborates through `Elaborator::check_module_delta` (and, with a previous image, `check_module_delta_from`) instead of `elab_module_source`:

| run (release, width one, `--timings`) | total | `decl_type` | kernel gate |
|---|---|---|---|
| `elab_module_source`, cold | ~24 s | ~3 s | ~9 s |
| session miss, no previous image | 104 s | 76 s | 12 s |
| session miss, previous image (other `--arg`s) | 85 s | 73 s | 4 s |

The time is statement elaboration, concentrated in specific declarations — `caller_native_literal_permissions_32` 469 ms, `caller_native_stack_permissions_31`/`_32` ~455 ms, `caller_native_return_reads_40` 420 ms, `caller_native_loaded_execution` 402 ms of `decl_type` each — with a median of 0.87 ms over 5,132 declarations. So something the delta-recording path does per statement is superlinear in what the statement mentions (the byte chain, the trace states), not a flat per-declaration charge.

The session route was reverted (`crates/cli/src/native.rs`, the comment at the certificate check names this issue); `build-x86` keeps only the declaration-verdict gate on the certificate. A suite run after a compiler change is all misses, so a 3–4× slower miss would cost more than the hits save.

Next step: `--timings` of the same certificate through both paths and diff `decl_type` per item (`scripts/timings --diff`); then find what `check_module_delta` does in statement elaboration that `elab_module_source` does not (journal recording, respelling for the image, slice hashing). Payoff beyond `build-x86`: `heather check --cache` goes through the same path on a cache miss, so any module with this shape pays it cold.

## Log

- 2026-09-23: Cause found and fixed. The miss was not statement elaboration on the delta path as such: `Elaborator`'s derived `Clone` deep-copied `module_journal`, which is every `DeltaEvent` the module had recorded so far, AST payloads included. Speculative probes clone the elaborator (`type_endpoint_can_anchor` in `lib.rs` is `self.clone().elab_infer(..)` at every equality endpoint; operator carriers, measure queries, slot probes do the same). So on the journalled path each probe was linear in the module's events, and a large module was quadratic. `elab_module_source` has no journal, which is why only the delta path paid. A frame-pointer `perf` of the miss: ~58% under `type_endpoint_can_anchor`, most of it `ModuleJournal::clone` → `ExprKind::clone`/memmove/malloc.

  Fix: `module_delta::JournalSlot`. A clone gets no live journal, only the live one's lengths; `restore_from_clone` (the one snapshot-restore, `elab_instance`) truncates the live journal back to them, as a failed `session_transaction` already did. Probes recorded into a copy that was discarded, so nothing observable changes.

  Measured on the `stack_save --callable-caller` certificate (release, width one, `heather check --cache` on an empty cache dir, library modules via a `-L` dir of the bundled SUPPORT sources): total 94 s → 32 s, against 31 s for plain `heather check`. The certificate module: 83 s → 21 s total, `decl_type` 67 s → 5.5 s; every counter column identical to the old `--cache` run. Library modules built into images on the delta path gain the same way, in proportion to their size.

  What remains open: whether to route `build-x86`'s certificate through `SemanticSession::check` again (the original goal; a miss should now cost what `elab_module_source` does). It only pays on a repeated build at unchanged compiler and inputs.
