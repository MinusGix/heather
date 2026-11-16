---
title: Layered elaborator registries hash the key once per module on every miss
status: closed
labels: [elaboration,performance,modules]
area: language
created: 2026-11-02
updated: 2026-11-02
---

Make lookups in the layered elaborator registries independent of the number of modules: on a miss, today's lookup hashes the key once per sealed layer.

## Problem

`Names` (`crates/elab/src/names.rs` ~160), `Types` (`types.rs` ~65), `Provenance` (`provenance.rs` ~58) and `GenDefs` (`gendefs.rs` ~1203) each hold `sealed: Rc<Vec<Rc<Layer>>>` and a current layer, with one sealed layer per module in the world (`lib/` has 282 `.hthr` files).

- `Names::entries(name)` chains every layer's `HashMap<String, Vec<NameEntry>>`.
- `global`, `inductive`, `constructor`, `member`, `has_record_field` and `by_tag` `find_map` over the layers. A miss, the usual answer for `has_record_field`, `declares_any_as` or `constructor` asked about a non-constructor, costs one SipHash of the key per module.
- `global_name_at(abs)` scans the layers for a dense `u32` Ψ coordinate that could index a `Vec`.
- `qkey` allocates `format!("{m}::{n}")` on every lookup ([[resolver-lookup-constant]] owns that part).

Measured with the gdb sampler (`docs/surveys/data-oriented-survey.md` §6): `names.rs` frames are in 3.5–4.7% of cold samples on calc_parser and lib/std/num + tactic. The share grows with the world, and a native check's world is the whole library.

## Proposal

- Sealed layers never change. A world carries one merged index of its sealed layers, holding each name's concatenated entry list so ambiguity stays visible. It is built once when the world is loaded, or merged LSM-style so the layer count stays logarithmic. Lookups probe the merged index and the small current layer.
- `semantic_snapshot`, the one place that seals a layer, extends or rebuilds the index.
- `by_abs` becomes a `Vec` indexed by the coordinate.
- Hash each key once per lookup, or intern it (resolver-lookup-constant's lever).

The index is derived, so the image format does not change. Acceptance: identical name resolution (the existing suites), and `scripts/perf ab` on a whole-library world.

## What it assumes from elsewhere

- **[[resolver-lookup-constant]]** owns per-lookup allocation and module-name interning. Assumed here: nothing beyond that; the layer scan is a separate cost.
- **[[elab-field-lifetimes-explicit]]** keeps these tables in the committed world. Assumed here: only that sealed layers are immutable.

## Log

- 2026-11-02: Built (`crates/elab/src/layered.rs`). All four registries are now a `Layered<L>`: the sealed layers plus a derived index of them, per table, from a key's one `index_hash` (a word hash, not SipHash) to the sealed layers holding a key with that hash. The index is kept in runs that merge like a binary counter (two runs covering equally many layers become one), so a world of n sealed layers has at most log₂ n + 1 runs. Runs are immutable and shared by every snapshot holding them, as layers are, so `semantic_snapshot` and `fork_over` still copy only pointers, where one merged index per world would have been copied (or rebuilt) for each retained module state. A lookup hashes once and probes the current layer plus only the sealed layers the runs name: a miss probes no sealed layer. `entries(name)` keeps every layer's entries in the old order, so ambiguity is unchanged; `find` keeps newest-first. A run's entry is twelve bytes (a hash and an inline layer position; a hash several layers share points into a side list). `by_abs` goes through the same index rather than a `Vec`: Ψ coordinates are not contiguous per layer once modules move, and the index already gives it one probe. `has_ty_codes` and its siblings read the runs' table sizes. `qkey`'s allocation stays with [[resolver-lookup-constant]].
  Measured (cloud, `scripts/perf ab --base 36dccd2`, 3 cold samples each, calc_parser and function_ir): all 39 counters identical; wall, gate and RSS deltas inside the per-sample spread (calc_parser wall +1.0 %, function_ir −2.3 %, neither a result). gdb sampler on calc_parser cold (`docs/surveys/data-oriented-survey.md` §6's method, four runs per side at 20 ms): samples with a layer walk in their top six frames went 4.0 % → 2.0 % (36/891 → 17/847), and any `names::` frame 5.6 % → 3.9 %. What remains is the hit's own probe and the resolution logic. The win grows with the world; calc_parser's is the prelude, std and parser. The library gate's `lib/_tests/native` folder hit the 300 s rail in this round's first `--pr` on a fresh box, on master as well (497 vs 486 CPU-s from the same seeded stores, identical counts): [[library-gate-native-tests-fresh-box-rail]].

