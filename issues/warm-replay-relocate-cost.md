---
title: A warm check is mostly moving imports: share the relocation rewrite
status: open
labels: [caching,performance,images]
area: infrastructure
created: 2026-10-30
updated: 2026-10-30
---

A warm check now spends most of its time moving imports, not checking them.
After moved replays were vouched for whole (`docs/module-dag-design.md` §13,
2026-10-30), a warm check of `lib/_tests/std/tactic/mono_tests.hthr` (release,
cloud box, width one) is about 3.7 s, of which `image_relocate_ns` is about
2.3 s, decode about 0.5 s, and everything else under 0.8 s. Stack samples sit
in `subst::sub_ty`/`sub_tm` under `ReindexGlobal` and in the drop of the
trees it rebuilt.

`ReindexGlobal` is the one global mapper that does not opt into the
shared-node memo (`crates/kernel/src/subst.rs`, "Keeping a shared DAG
shared"): its map is a caller's callback, so the module doc excludes it. The
moves `crates/cli/src/semantic.rs` makes go through `MoveMap::at`, a pure
function of the free index, and `dependency_references` only collects
indices into a set, which a memo hit cannot change. Two levers, in order:

1. **Memoize it.** Opt `ReindexGlobal` into the memo for a pure map
   (a flag or a separate mapper). Since images are DAGs
   ([[image-tree-walks-let-shared-terms]]), the bigger win is one memo across every
   payload of a `ModuleDelta::relocate`, not one per binding: decoded
   bindings share subterms with each other.
2. **Move less often.** A closure of `n` modules replays about twice that
   many images (`docs/module-dag-design.md` §6: 43 replays for 26 modules
   here), and each moved replay rewrites its image again. Keeping a moved
   delta per (image, map) for the process, or reaching more worlds by
   extending a snapshot instead of rebuilding, removes rewrites rather than
   making them cheaper.

Measure with `--timings` on a warm store by hand (`scripts/perf ab`'s warm
mode starts from a fresh store and never reaches the vouched run); the
column is `image_relocate_ns`, which since this issue was filed covers the
composition moves as well as the early cutoff's.
