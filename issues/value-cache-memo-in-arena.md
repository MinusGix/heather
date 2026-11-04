---
title: Memoized values live in Rc beside the arena: ~1.94 M heap allocations per module that no pooling reaches
status: closed
labels: [kernel,conversion,performance,representation]
area: kernel
created: 2026-09-11
updated: 2026-10-30
---

Datum from the arena-pooling design pass (2026-09-11, docs/conversion-query-arena-pooling-design.md §1-§2): on the five-node FunctionIR/x86 module, `ValueArena::cache_ty`/`cache_tm` insert 1,894,881 `Rc<VTy>` and 49,249 `Rc<Val>` — one heap allocation per forced node — against ~60,000 typed_arena chunk allocations for the whole module (33:1). This, not arena churn, is the ~30% allocator share the 2026-09-06 profile attributed to conversion; every arena-policy variant measured neutral-to-worse and lever 2 of [[conversion-query-arena-pooling]] was refused on it.

The lever: put the memoized value in the query arena and key the cache by `&'v` reference, the same medicine [[value-domain-allocation-constant]] applied to elimination spines and environment cells on 2026-09-02. It is a representation change across `eval.rs`'s force paths and the `Dom` API, not a cache-lifetime change, so it wants its own falsifier: an arena-resident memo must not change eviction semantics (the bounded FIFO keeps its pointer keys valid because closures live as long as the arena) or the `value-metrics` counters' meaning.

Trigger: a round whose issue names kernel constant factors as the point, with the five-node module (`mixed ALU kernel=`) and cold Omega as the workloads and the design doc's §4 as the before-column shape.

## Log

- 2026-09-11: 2026-09-11: [[kernel-arena-terms-frozen-prefix]] proposes taking the allocation constant at the representation level (indices, no refcounts) rather than one memo at a time; this issue's 33:1 datum is its before-column.
- 2026-10-30: Landed, with the design pass's §5.1 slice (`docs/kernel-arena-terms-design.md`) taken whole and one step further. `Val`, `VTy`, `VNeutral` and the value-domain `Elim` cells are born in `ValueArena` (`vals`, `vtys`, `neutrals`, `elim_cells`) and every handle is a `&'v` borrow, so forcing a node is a bump of the query region, not a `malloc` plus two atomic reference counts (`Rc` here is `std::sync::Arc`). The memo tables hold borrows. Identity is `Val::ptr_eq`/`VTy::ptr_eq`, and an address now names one value for the whole query: nothing is freed under it. A neutral was two heap allocations and is now two bumps. Pushing an elimination onto a glued neutral now reuses the spine node's elimination for the unfolding: it used to copy it into a second `Rc`. An elimination an evaluator frame makes for itself rides in the frame by value, because a region cell would outlive the frame by the rest of the query.

  The falsifiers from the design pass. **Memory**: peak RSS was unchanged at width one on the x86 certificate (614 → 610 MB) and on cold omega (194 → 193 MB); at the default width eight, one sample of the certificate under the suite's load read 1447 → 1356 MB, so the arena retains nothing the `Arc`s were freeing early. **Eviction semantics**: moot, because nothing has been evicted since the cache-policy round. **Counters**: the `value-metrics` memo counters now say they count table events, not allocations. **Failure memo**: unchanged, since the arena allocation sits on the success path where `Rc::new` did.

  Measured on the cloud box (2026-10-30, `scripts/perf ab`, dev profile, width one, cold, three interleaved samples per side). Every counter column was identical across binaries and samples. The kernel gate fell 19% on `calc_parser`, 23% on `omega` and 18% on the x86 certificate (`examples/x86-native/program.hthr`, 34.7 → 28.9 s), with the samples separated in all three. Whole-file wall fell 4–7%, where the elaborator dominates; on two of the three files that is inside the spread. Heavy items fell between 12% and 46% (`omega::cut_cooper_core` −46%, `Site::moves_spills` −18%). `scripts/bench --check` cannot resolve this on the cloud box: master checked against its own fresh baseline moved ±30–40% per case, so its rows say nothing about this change (`docs/cloud-benchmarks.md`'s "nothing else runs" was kept, and the box was still that noisy).
- 2026-10-30: Not taken here, and handed on: the word-keyed conversion memo that [[kernel-native-bitvector-values]] assigned this issue on 2026-09-13 moves to [[value-domain-allocation-constant]], which stays open for the per-node constant that is left.
