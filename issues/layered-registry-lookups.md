---
title: Layered elaborator registries hash the key once per module on every miss
status: open
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

Measured with the gdb sampler (`docs/data-oriented-survey.md` §6): `names.rs` frames are in 3.5–4.7% of cold samples on calc_parser and lib/std/num + tactic. The share grows with the world, and a native check's world is the whole library.

## Proposal

- Sealed layers never change. A world carries one merged index of its sealed layers, holding each name's concatenated entry list so ambiguity stays visible. It is built once when the world is loaded, or merged LSM-style so the layer count stays logarithmic. Lookups probe the merged index and the small current layer.
- `semantic_snapshot`, the one place that seals a layer, extends or rebuilds the index.
- `by_abs` becomes a `Vec` indexed by the coordinate.
- Hash each key once per lookup, or intern it (resolver-lookup-constant's lever).

The index is derived, so the image format does not change. Acceptance: identical name resolution (the existing suites), and `scripts/perf ab` on a whole-library world.

## What it assumes from elsewhere

- **[[resolver-lookup-constant]]** owns per-lookup allocation and module-name interning. Assumed here: nothing beyond that; the layer scan is a separate cost.
- **[[elab-field-lifetimes-explicit]]** keeps these tables in the committed world. Assumed here: only that sealed layers are immutable.
