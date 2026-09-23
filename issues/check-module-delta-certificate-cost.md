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
