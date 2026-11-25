---
title: The contract's injection lemma for a put of any piece and a take of any piece, the per-store lemmas its instances
status: open
labels: [native,x86,memory,ownership]
area: heather-in-heather
milestone: [nh-ownership]
created: 2026-11-25
updated: 2026-11-25
---

The contract's injection lemmas are per machine store today: `Loan::store_injected` for plain bytes and `Loan::store_ref_injected` for one reference (`lib/std/arch/x86_64/x86_64_memory_contract.hthr`), while every heap operation is now a read or a write of a `Piece` (`Heap::piece`, `Heap::placed`; [[bytes-level-on-the-contract]]). The bytes level's typed `Copy` puts a piece holding any number of references, so its lowering needs the general lemma.

## Scope

- `Piece::lower(spans)`: the piece's bytes with each slot's eight replaced by its target's address, what the machine stores for it.
- `Loan::put_injected`: a heap injected, a put that answers (`Heap::put` under a lending whose written spans cover the run's `Blocks`, `Heap::put_lent`), and the memory with `piece.lower(spans)` stored at the address: the placed heap is injected. It needs the piece's slots inside it and apart from each other, which every take of a heap whose pointers are apart gives: state "pointers apart" beside `Heap::Canonical` and its preservation (the entries-apart invariant [[bytes-level-passes]] also needs).
- `Injected::takes`: a take that answers reads, at every defined byte of the range, the taken piece lowered. `Injected::reads` and `ref_read` become its cases.
- Then `store_injected` and `store_ref_injected` are its instances at `Piece::plain` and `Piece::reference`, and the second stops being derived from the first.

## Done when

One injection lemma per primitive (take, put), the per-store lemmas their instances, the copy's lowering able to cite them.

## What it assumes from elsewhere

- [[bytes-level-on-the-contract]]: the heap, pieces and `placed` as built.

## Log

- 2026-11-25: [[bytes-level-lowering]] round 1 needs this lemma for the typed copy (`Instr::Copy`), and stopped at the leaves that do not: `Instr::emit` refuses a copy, and the copy's lowering is [[bytes-level-copy-and-halfwords]], waiting on this. The other nodes cite the per-store lemmas (`Loan::store_injected`, `store_ref_injected`) and the reads as they are.
