---
title: Per-span Readable lemmas beside Injected: keep one level after stage 3
status: open
labels: [native,x86,memory]
created: 2026-11-25
updated: 2026-11-25
area: heather-in-heather
---

The memory contract (`lib/std/arch/x86_64/x86_64_memory_contract.hthr`, [[x86-memory-contract]]) says what a store leaves at two levels: per span (`Readable`: `Loan::store_reads`, `store_keeps`, `own_reads`, `stable_reads`, `unwritten_reads`, `readable_window`, `readable_put_window`, and `Sub`'s `sub_*_reads`) and per heap (`Injected` and its operation lemmas). No statement is proved twice, and FunctionIR's `Stack::InMemory` lemmas now go through `Injected`; the per-span level is used by the views (`Lendable::put_reads`), `Stack::LentAll`/`Lends` and the probes.

When stage 3 (`docs/language/ownership-design.md` §17.5) deletes the old lowering and `x86_64_memory_tiers.hthr`, check which of the per-span lemmas anything still cites; if only the bytes level's lowering is left, it should need `Injected` alone, and the `Readable` level and `SubCovers` go with the tiers. Also: `Stack::lent_four` keeps a canonical computation of its own that `Loan::canonical_at` could give.
