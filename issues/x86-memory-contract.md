---
title: The x86 memory contract stated once: Loan, WroteIn, Injected and Sub, with the older tiers as instances
status: open
labels: [native,x86,memory,ownership]
area: heather-in-heather
milestone: [nh-ownership]
created: 2026-11-25
updated: 2026-11-25
---

Stage 1 of `docs/language/ownership-design.md` §17.5: the x86 memory contract stated once. Today it is in tiers that grew one at a time, each derived from the next (§17.1): `Stack::Unchanged` and `CalleeKeeps`; `Wrote`, `Stable`, `Through`, `Lends`, `Site::Calls`, `Framed`; `WroteIn`, `StableIn`, `Lending`, `InMemory`, `Trail`, `Trailed`, `Site::CallsOver`; `Site::CallsLent`; `Views`, `Viewed`, `Loan::view`, `Loan::onto`, `Lendable`; and experiment three's `Injected`, `Carved`, `Loan::carve`, `wrote_in_parents`, of which `Carved` is `Viewed` and `Loan::carve` is `Loan::view`.

## Scope

- **One module**, the memory contract, exporting: `Loan` and its laws, as built; `WroteIn` with reflexivity, transitivity, deepening and widening, and `Stable` with the frame rule; `Injected` (a heap of bytes with a shadow of references, into machine memory; `lib/native/reference_cells/reference_cells_x86.hthr` has the experiment's) with one lemma per memory operation at every width the machine has, and its stability under an own store; `Sub` (a part of a span: the one record that `Viewed` and `Carved` both are) with `Loan::sub` and `WroteIn::up`. The heap canonical: the bytes under an entry are zero.
- **The older tiers become instances**: `Wrote`, `Unchanged`, `CalleeKeeps`, `Framed`, `Site::Calls` are `WroteIn` at no spans; `Lends`, `LentAll`, `InMemory`, `Trail`, `Trailed` and their stability lemmas are `Injected` at an empty shadow and its lemmas; `Viewed`, `Loan::view`, `Loan::onto`, `wrote_in_view`, `Carved`, `Loan::carve`, `wrote_in_parents` are `Sub`. Each old name survives only as an abbreviation with a one-line derivation, for the existing lowering to cite until stage 3 deletes it. No statement is left with two independent proofs.
- **`Site::Meets`** (§17.2) is stated here as a definition, with the probe that the existing `Site::CallsLent` at one lending implies it at an empty shadow. Its use is stage 2's.
- `x86_64_views` and the experiment's `reference_cells_x86`/`_bridges` lemmas that restate these are folded in; the experiment's toy language and its program stay until stage 2 replaces them.

## Done when

The contract module and the abbreviations pass the suite with every existing certificate unchanged (`scripts/linked --check`, the native gates), and the log lists, for each old name, the one line it now is.

## What it assumes from elsewhere

- **[[ownership-reference-cells-spike]]** (closed) gives `Injected`, the shadow and the operation lemmas for one width.
- **[[bytes-level-language]]** owns what cites `Site::Meets`.
