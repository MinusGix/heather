---
title: Imports were read by parsing every module whole, twice a check
status: closed
labels: [cli,performance,cache]
area: infrastructure
created: 2026-11-11
updated: 2026-11-11
---

A warm `heather check --cache` replays every module of the closure from its image, so nothing in it needs a module's declarations. It parsed every module whole all the same, twice: once in the loader (`loader::Walk::visit`) and once in the session (`semantic::written_imports`), each time to read the `import` lines and drop the rest. A cold run parsed each module a third time, in the elaborator, which is the only parse that uses the result.

Imports come first in a file, and `parse_file` refuses one after a declaration. `docs/modules-design.md` §3.1 gives the reason: it "makes the import DAG readable without parsing declarations". Nothing read it that way.

## What that cost

Callgrind, width one, `docs/showcase/calc_parser.hthr`, every module replayed and vouched for (the third run over a fresh cache directory):

| | instructions | of which scalar SHA-256 (the profiler's; the box hashes with SHA-NI) |
|---|---|---|
| whole run | 4,782 M | 2,692 M |
| `parse_file` under `written_imports`, 72 calls | 615 M | |
| `parse_file` under `Walk::visit`, 56 calls | 496 M | |

So 1,111 M of the 2,090 M that are not the profiler's hash: over half of a warm check was parsing bodies nobody read.

A cold check of `examples/x86-native/levels.hthr` (103,932 M): 1,653 M under `written_imports` (116 calls), 1,016 M under the loader (78), 827 M under the elaborator (59).

## The second cost, found in the same profile

`ModuleImageCache::load` projects the decoded delta's interface (re-encodes it and hashes the bytes) to hold the stored interface hash to it, and returns the result as `LoadedModule::interface_hash`. The session then called `ModuleImageCache::interface_hash(&delta)` on the same delta for the module's `Finished::identity`: the same encode and the same hash again, 733 M of the run above for 36 modules (227 M of it encoding, the rest the profiler's hash). `hit_into_process` already took the loaded value.

## Fix

- `heather_syntax::leading_imports(src)`: the import items a source opens with. `lexer::lex_while` stops lexing at the first token that begins anything else (a token opens an item, as far as imports go, when it is the first or follows a `;`), and the parser's own `import` rule reads what was lexed. The loader and `written_imports` call it.
- The session keeps what the load knew of a replayed image (`semantic::Hit`: the stored bytes' digest, which it already kept, and the interface identity) and projects only for a module it elaborated.

What changes in behaviour: a source that does not parse used to have no imports as far as the loader could tell, and now has the ones it opens with. Its parse error is still the elaborator's to report, after its imports are built instead of before.

## Result

Fully warm showcase check, callgrind: 4,782 M to 2,907 M; without the profiler's hash, 2,090 M to 946 M (imports) to 720 M (identity).

`scripts/perf ab`, cloud box, quiet, width one, interleaved, `heather-plug1` (the queue's tip before this) against both changes. All 45 count columns identical in both modes.

| mode | before | after | |
|---|---|---|---|
| warm, 7 samples | 0.76 / 0.70 / 0.67 / 0.67 / 0.76 / 0.79 / 0.72 s | 0.41 / 0.47 / 0.45 / 0.48 / 0.49 / 0.47 / 0.48 s | −35.2%, separate |
| edit (one declaration appended), 5 samples | 0.90 / 0.82 / 0.84 / 0.88 / 0.78 s | 0.64 / 0.64 / 0.60 / 0.66 / 0.60 s | −24.6%, separate |

## What is left in a warm check

Of the 720 M: the load's own projection (218 M encoding, kept: it is the check that the decoder and the encoder agree about an image this build wrote), decoding the deltas (181 M), the canonical worlds (71 M), the replay itself (70 M), and nothing else above 30 M. Each image's bytes are also hashed twice in the load (the file's checksum, then the semantic part's digest), which the box does with SHA-NI.

## Log

- 2026-11-11: Fixed: `heather_syntax::leading_imports` reads a module's imports from its import lines (a lexer that stops at the first token that opens another item, then the parser's own `import` rule), used by the loader and by the session's image keys; a replayed module's `Finished::identity` is the interface hash its load already projected. Warm showcase check −35.2% and a check after a one-declaration edit −24.6%, both with the sample sets apart and all 45 count columns identical (`scripts/perf ab`, width one, cloud box). `crates/cli/tests/lib_closures.rs` holds the two readings equal, spans included, over every source under `lib`, `examples` and `docs/showcase`. Left in a warm check: the load's own interface projection, the decode, and building the worlds.
