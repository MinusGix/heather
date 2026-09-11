---
title: Memoized values live in Rc beside the arena: ~1.94 M heap allocations per module that no pooling reaches
status: open
labels: [kernel,conversion,performance,representation]
created: 2026-09-11
updated: 2026-09-11
---

Datum from the arena-pooling design pass (2026-09-11, docs/conversion-query-arena-pooling-design.md §1-§2): on the five-node FunctionIR/x86 module, `ValueArena::cache_ty`/`cache_tm` insert 1,894,881 `Rc<VTy>` and 49,249 `Rc<Val>` — one heap allocation per forced node — against ~60,000 typed_arena chunk allocations for the whole module (33:1). This, not arena churn, is the ~30% allocator share the 2026-09-06 profile attributed to conversion; every arena-policy variant measured neutral-to-worse and lever 2 of [[conversion-query-arena-pooling]] was refused on it.

The lever: put the memoized value in the query arena and key the cache by `&'v` reference, the same medicine [[value-domain-allocation-constant]] applied to elimination spines and environment cells on 2026-09-02. It is a representation change across `eval.rs`'s force paths and the `Dom` API, not a cache-lifetime change, so it wants its own falsifier: an arena-resident memo must not change eviction semantics (the bounded FIFO keeps its pointer keys valid because closures live as long as the arena) or the `value-metrics` counters' meaning.

Trigger: a round whose issue names kernel constant factors as the point, with the five-node module (`mixed ALU kernel=`) and cold Omega as the workloads and the design doc's §4 as the before-column shape.

## Log

- 2026-09-11: 2026-09-11: [[kernel-arena-terms-frozen-prefix]] proposes taking the allocation constant at the representation level (indices, no refcounts) rather than one memo at a time; this issue's 33:1 datum is its before-column.
