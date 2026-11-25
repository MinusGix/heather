---
title: Copy, Clone and the exact-clone extension, derived from a layout
status: closed
labels: [ownership,library]
area: heather-in-heather
milestone: [nh-ownership]
created: 2026-11-25
updated: 2026-11-25
---

`Copy`, `Clone` and the exact-clone extension of `docs/language/ownership-design.md` §10.8. There is no such class in `lib/` today; the nearest thing is `Ty::holds_bytes` in `lib/lang/facts/unique.hthr`, a function that says which `rt` types may hold a buffer.

## Scope

- **`Clone`**: a class with the operation and no law.
- **The exact-clone extension**: `clone(x) = x`, a law its consumers ask for as a fact (a proof rewriting a clone away, the compiler inserting one where a function's policy allows, the optimizer deleting one when the original is dead). A simp-shaped theorem a client cites, and a probe that a clone in a statement rewrites away.
- **`Copy`**: a fact about a representation, not about a type: a value held as words whose bits may be duplicated. Stated for `rt`'s type codes (`Ty` in `lib/native/runtime/rt.hthr`) and for a codec (`Stored` in `lib/std/machine/stored.hthr`), with a decider on `Ty` that agrees with `Ty::holds_bytes` where both speak, so the judgment has one question to ask.
- **Derivation**: instances for words, `Bool`, records of copyable parts and laid records (through the `laid` generator or beside it), each with its exact-clone law; a key (`lib/std/data/store.hthr`) is copyable, a store is not. `Erased<A>` (`lib/std/core/erased.hthr`) is copyable whatever `A` is, since it has no runtime presence.
- **A type with representation slack**: one worked example that keeps plain `Clone` and states its law up to its own equivalence (the word map under `WordMap::abs` is a candidate), to show the extension is not forced.
- Drop means nothing (§10.8) and gets no class in this round; say so where the classes are declared.

## Done when

The classes and instances pass the library gate, the exact-clone law rewrites a clone away in a probe, the `Copy` decider on `Ty` is proved against its statement, and the negative controls (an owned buffer and a store are not copyable) are `¬` theorems or named refusals.

## What it assumes from elsewhere

- **[[ownership-discipline-over-code]]** owns the judgment that asks these facts. Assumed here: only that it asks them as ordinary propositions and class instances.
- **[[ownership-stores-and-keys]]** owns keys and stores.

## Log

- 2026-11-25: Built (2026-11-25). Library only; no Rust crate touched.

  - `lib/std/core/clone.hthr`: `Clone<A>` (the operation), `CloneRel<A>(same)` (`clone(x) ≈ x`), `ExactClone<A>` = `CloneRel` at `RelId`, its law `ExactClone::clone_eq` (cited; `simp_only(ExactClone::clone_eq)` rewrites a clone away at an open or a concrete carrier). Instances: `Bool`, `Nat`, `True`, `Erased<A>` (nothing asked of `A`), `Pair`, `Option`, `List` (deep). Drop: a comment where the classes are declared, no class (§10.8's reason).
  - `lib/lang/facts/copy.hthr`: `Ty::Copy` over `rt` codes and the decider `Ty::copies`, proved to reflect it (`Ty::copies_reflects`; `copy_of_copies`, `not_copy_of_copies`, `copies_of_copy`). Agreement with `Ty::holds_bytes`: equal at every code naming no table entry (`copies_holds_bytes`), never contradicting its "may hold" at a record (`holds_bytes_of_not_copies`), equal at an enum whose slots copy (`enum_agrees`). `Stored::copies` (a copy of a value's bytes reads the value) and `Stored::unbounded` (no codec holds a type with a value for every number, by `Fintype::pigeonhole` over `BitVec(8k+1) → BitVec(8k)`); `Stored::no_byte_list`. `Copy<A>(rep: Rep<A>)` with `Rep::Code` (a `Coded<A>`: code, table, and a retraction), `Rep::Bytes`, `Rep::Absent`; `Copy::of_code` / `Copy::code_copies` (the two askers, one answer), `Copy::of_bytes`, `Copy::exact_clone` (from `Rep::copy_eq`). Instances `Copy` at words, `Bool`, counts, `Erased<A>`; `ExactClone<BitVec(w)>` derived from the word's code. Generator `laid_copy`.
  - `lib/std/data/store_copy.hthr`: `Copy<Key>(Key::rep())` at a record of two counts, decided by the decider (closed `refl`), `ExactClone<Key>` from it; `Store::no_codec`, `Store::not_copy_bytes`; `ExactClone` for `Slot<V>` and `Store<V>` (exact, though not copyable).
  - `lib/native/runtime/word_map_clone.hthr`: `CloneRel<WordMap>(WordMap::SameRows)`, the clone copying live rows only (`scrub`), `scrub_abs`, and `scrub_not_exact`.
  - Probes: `lib/_tests/lang/facts/copy_tests.hthr`, `lib/_tests/std/data/store_copy_tests.hthr`, `lib/_tests/native/runtime/word_map_clone_tests.hthr`. Negative controls: `buffer_not_copy`, `record_with_buffer_not_copy`, `buffer_no_instance`, a named refusal (`buffer_claimed`: the verdict is not `True`), `byte_list_no_codec`, `store_no_codec`, `buffer_key_not_copy`, `plain_clone_not_exact`, `not_exact` (the word map).

  Decisions:
  - Name `ExactClone`: the note's word, spelled as a chain member (`CommMonoid` on `Monoid`); `Exact` is already the library's "loses nothing" (`Stored::Exact`). `Lawful*` not taken: the relational member has a law too. The law up to an equivalence is `CloneRel`, by the `algebra_rel` convention, rather than a separate unindexed class.
  - `Copy` is indexed by a representation value, one class for codes, codecs and erased data, rather than one class per kind; an instance's index must be a global, so each representation is one (`Rep::word(w)`, `Key::rep()`, `T::rep`).
  - An enum copies when its slots copy; a `Named` field inside a record (refused by every judgment) does not; `Lines` copies (the name of a cell written once: a frozen view), as `holds_bytes` already says.
  - At the bytes, the negative control is semantic (no codec exists) rather than a missing instance; at the codes it is `ByteList`. A store's code-level control is not stateable: `Count` means `Nat`, so a store could be coded into one count, which only the codec level refuses.
  - `ExactClone` does not need `Copy`: a list's and a store's clones are exact though neither copies.
  - Laid records: the generator cannot register an instance at a named carrier (the elaborator spells a generated carrier as a headless leaf), so `laid_copy` publishes `T::rep`, `T::copy`, `T::clone` and the record's module registers two `instance` lines. The word map deliberately has no `ExactClone` registered.

  Residue filed: [[laid-publishes-copy]] (the join into `laid`, with the opt-out the word map needs), [[generated-instance-at-named-carrier]] (the elaborator), [[rewrite-inherited-field-head]] (`rewrite` misses `x.clone()` at a concrete carrier; `simp_only` works), [[holds-bytes-enum-payload]] (`holds_bytes` at an enum with a buffer slot).
- 2026-11-25: Verified: `scripts/test --pr` on the final tree, `== suite: 3514 passed, 0 failed, 2 ignored ==`, the whole-library gate (`crates/cli/tests/library.rs`) and `lib_closures` among them. Closed; residue owned by the four issues above.
