---
title: check_module_delta makes a generated certificate's statements ~25× slower than elab_module_source
status: closed
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
- 2026-09-23: `build-x86`'s certificate goes through `SemanticSession::check` again (`crates/cli/src/native.rs`). Interleaved before/after, two samples each, release, width one, fresh cache dir per sample, `stack_save --callable-caller`:

  | run | before | after |
  |---|---|---|
  | cold (library + certificate) | 32.4 / 31.6 s | 31.9 / 32.0 s |
  | repeat, same inputs | 13.4 / 13.5 s | 1.3 / 1.4 s |
  | other `--arg`s over the same cache | 16.2 / 17.5 s | 16.4 / 16.4 s |

  A miss costs what `elab_module_source` did; a hit replays. A certificate image is ~16 MB; the store's size budget evicts oldest-first. Full suite green on the first (all-miss) run.

  Other `--arg`s get nothing from slice replay: the inputs first appear ~2% into the certificate (line 758 of 33,462; 431 lines differ in all), and a slice replays only while every earlier item reproduced the previous prefix exactly. Emitting the input-dependent declarations last would let an other-inputs build replay the rest — an idea, not measured.
- 2026-09-23: Suite effect. A full `scripts/test` right after a compiler change is all certificate misses and costs what it did (89 s tests wall, 796 CPU-s, green). A second run at the same compiler replays every native build's certificate: 69–79 s wall, 567–619 CPU-s across two runs, and the eight two-build native acceptance tests (33–41 s each before) drop out of the slowest list. What leads now: the composed-summary fixtures in `callable.rs` (in-process, `elab_module_source` over forks, untouched here) and `cli_showcase_calc_text`.

  `crates/cli/tests/native.rs::source_to_native_binary` asserted an item row per certificate declaration, which a replayed certificate does not have; it now accepts a replayed module row (decode and recheck both non-zero) as the whole account, and checks per-declaration coverage whenever the certificate was elaborated. Both paths run: warm against `target/native-test-images`, and once against an emptied one.
- 2026-09-23: Input-dependent declarations last (`crates/cli/src/native/order.rs`). The certificate is generated twice more at unrelated inputs (`!inputs`, and the inputs plus two odd constants); a declaration whose text differs from either probe's, or that a probe lacks, is a seed, and the seeds with everything that refers to them (and anything a moved item refers to later in the module) move to the end in order. On `stack_save --callable-caller`: 1,780 of 5,109 declarations move; 3,315 stay in a prefix a build at other inputs replays. One probe was not enough — `word_2` was needed by (MAX, 1) and its lone probe but not by (20, 22), stayed in the prefix, and broke it at item ~530.

  That alone made other-inputs builds *slower* (16 → 17–18 s): the 3,315 replayed slices cost 19 s against 12 s to elaborate them cold. Same shape as the journal: `try_replay_slice` wrapped each slice in `session_transaction`, whose checkpoint holds the committed world, so the slice's first write copy-on-wrote every registry's current-module layer (names, AST) — O(module) per replayed item. `replay_slice` fails only before its first write, so the transaction was redundant; removed, with the invariant on `replay_slice`'s doc. The 3,315 slices then replay in 0.2 s.

  Profiling that path also turned up a fail-open at width > 1 under a verdict gate: a replayed slice's recheck joined the module pass's pool and swallowed its deferred rejections. Fixed with a regression test: issues/slice-replay-join-swallows-deferred-rejection.md.

  Interleaved A/B, previous commit (session routing, no reorder) vs this, two samples, release, width one, fresh cache per sample:

  | run | before | after |
  |---|---|---|
  | cold (20, 22) | 30.6 / 30.3 s | 32.2 / 30.7 s |
  | then (MAX, 1) | 16.2 / 15.4 s | 9.6 / 9.5 s |
  | then (5, 7) | 16.1 / 15.4 s | 9.4 / 9.4 s |
  | then (20, 22) again | 1.33 / 1.26 s | 1.56 / 1.47 s |

  The repeat pays the two probe generations (~0.2 s) before the image hits. What an other-inputs build still elaborates is the input-dependent 1,780 declarations and the library replay.
- 2026-09-23: Copy-on-write counter and audit. Every registry copy-on-write write now goes through `stats::make_mut` (`Rc::make_mut`, counted and timed when it actually copies, with `#[track_caller]` on the elaborator's and `Shared`'s `deref_mut`). Two `--timings` columns, `cow_ns` and `cow_copies` (`scripts/timings --columns "cow ms,copies"`), and a `*.cow-sites.txt` beside the TSV: copies, ms, copied type, write site, costliest first (docs/infrastructure/instrumentation-design.md, "Elaborator state").

  Audit, release, after this issue's two fixes:

  | workload | copying |
  |---|---|
  | perf full corpus, `check --cache` cold, width one (omega, nat, int, list, bitvec, algebra, calc_parser, ir_v1, function_ir, x86_64 model, calc_text) | ≤ 0.02 s per file |
  | the `stack_save` certificate, `--cache` cold | 0.013 s of 31 s |
  | x86_64 model / calc_text warm (image replay), width 1 and 8 | ~0 |
  | x86_64 model cold at width 8 | 0.033 s |
  | calc_text edited (appended decl, slice replay), width 1 and 8 | ~0 |
  | `slow_acceptance_multi_stack_save_summary` (in-process forks) | 0.012 s of 20.7 s |

  What remains is healthy by construction: one copy of each registry's current layer per module boundary (`names.rs` `NameLayer` dominates, ~0.3 ms per module), and the persistent `GlobalCtx` pushed on every commit while `delta_psi` shares it (O(1)). No path measured has an O(module) copy per declaration left.

  Guard: `crates/elab/tests/slice_replay.rs::registry_layers_are_not_copied_per_declaration` elaborates and slice-replays a 121-declaration module and bounds registry-layer copies (types other than `GlobalCtx` and `CommittedWorld`) below N/2. With the per-slice checkpoint put back it fails naming 121 `NameLayer` copies at `names.rs:416` — verified. The counter does not see a derived `Clone` of a plain collection, which is what the journal bug was; that class still needs a profiler.
