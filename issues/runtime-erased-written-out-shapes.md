---
title: Erased parameters of a plain runtime fn: the shapes not written out yet
status: open
labels: [ownership,native,runtime-fn]
area: heather-in-heather
milestone: [nh-ownership]
created: 2026-11-25
updated: 2026-11-25
---

A plain `runtime fn` of words that takes an erased parameter is compiled from its reflection written out (`f::words`, `RtWriting::value` in `lib/native/runtime/runtime.hthr`; [[runtime-erased-pure-shadow]], `docs/native/runtime-fn-setups-design.md` §16.22). Refused by name, each "cannot be a runtime fn that takes an erased parameter yet: …":

- **A body with a `match` on an enum, a fold, or a byte of a lent span** (`Pick`, `Fold`, `Case`, `Byte`, `Slot`, `Iterate`): each is written as its meaning reduces to (`EnumInfo::choose`, `List::foldl` with the step's table entry, …), as `RtWriting::value` writes the others; nothing in the route changes.
- **An enum or a record parameter beside an erased one**: `f::agrees` states an enum parameter at its value by a case split and a narrow record by a read-back (`runtime_at_enums`), and the erased locals' types are taken at the words; they would be taken at each split's value.
- **A plain function lent a span**: its pin and agreement are at every file (`Ty::lend`); the written-out term would take the span's bytes in its place.
- **`compile-x86` of an export that takes an erased parameter**: the certificate cites `{source}::agrees({words})` (`crates/cli/src/native/verified.rs`), which now takes the erased locals too; its callers export fine. The certificate would quantify over the erased values, or the export would be stated at `f::words`.
- **A caller's pin cost**: a caller's pin compares `g(x, p)` with `g::words(x)`, unfolding the callee once per call site. A citation of `g::reflects` there would need a rewrite under the caller's binders; take it if a library caller shows the cost.

Loops and recursions taking an erased parameter wait for [[loops-on-one-combinator]] round 4.
