---
title: A copy of a record holding references whose layout is not static: a range copy moving shadow entries, or fragments
status: closed
labels: [ownership,native,design]
area: heather-in-heather
milestone: [nh-ownership]
created: 2026-11-25
updated: 2026-11-25
---

A copy of a record that holds references, at the bytes level of [[ownership-reference-cells-spike]].

The experiment's finding: a copy whose layout is known (which eight-byte cells are references) is a typed copy, a reference load and store per reference cell and words or bytes for the rest, and it lowers to the very `MOV`s a word copy would emit (the probe `typed_copy_reads_nine`, `lib/_tests/native/reference_cells/reference_cells_tests.hthr`). No fragments are needed. A byte loop over a reference's bytes has no meaning (`byte_of_reference_refused`), and a store that cuts a reference has none either (`cut_refused`): the bytes left under a cut entry would be part of an address the meaning cannot name. That refusal was forced by the proof (`Loan::store_word_injected` needs the cleared entries to lie wholly under the store).

Open: a copy whose layout is not known statically (a generic container's move of `T`). Two routes: a primitive range copy of the bytes level whose meaning moves the bytes and every entry wholly inside the range (refusing or dropping cut ones), lowered as a byte loop (the machine's bytes under an entry are the address, so the injection is kept); or CompCert's fragments, a byte of a reference as a value, which lets the copy be a loop in the meaning. Lean: the primitive range copy, since level 2's types make the layout known everywhere but at a generic move, and fragments would put a third kind of value into every byte operation.

## Done when

A generic move of a record holding references compiles with its theorem by one of the two routes, the other's cost written down.

## What it assumes from elsewhere

- **[[ownership-reference-cells-spike]]** owns the shadow and the cut refusal. Assumed here: only that an entry is eight whole bytes and a store may not cut one.

## Log

- 2026-11-25: 2026-11-25: Closed: the first route is the bytes level's typed `Copy` ([[bytes-level-language]]; one definition, `Heap::copy`, in `x86_64_memory_contract` since [[bytes-level-on-the-contract]]): a take of the range's piece (its bytes, every reference wholly inside it, its undefined bytes) and a put of it, refused where either range cuts a reference. No fragments. What remains is its lowering's injection lemma for a put of a piece holding references, filed as [[contract-put-of-a-piece-injected]].
