---
title: The laid generator publishes a record's Copy and exact clone
status: open
labels: [ownership, library, generators]
area: heather-in-heather
milestone: [nh-ownership]
created: 2026-11-25
updated: 2026-11-25
---

`ownership-copy-clone` derives a laid record's `Copy` (at `Rep::bytes(T::stored())`) and its `ExactClone` (its bytes read back) by a separate call beside the record, `generate laid_copy("T")` (`lib/lang/facts/copy.hthr`), and the record's module registers the two values it publishes with one `instance` line each. The join is for `laid` itself to publish them, so a laid record is copyable with no call of its own.

## Scope

- `laid` publishes `T::rep`, `T::copy`, `T::clone` (or calls `laid_copy`), and registers the instances once a generator can (blocked on [[generated-instance-at-named-carrier]]); until then the two lines stay the record's.
- A record with parameters (`Limbs(n)`): the values take them, as `T::stored` does.
- **A record that keeps its own clone.** The word map registers a slack `Clone` (`CloneRel<WordMap>(WordMap::SameRows)`, `lib/native/runtime/word_map_clone.hthr`); an `ExactClone<WordMap>` from the generator would give `Clone<WordMap>` two sources. The generator needs an opt-out (`laid(clone := False)`) or must publish the values without registering them.
- `laid.hthr` would import `copy.hthr`, which imports `rt`; check that the import does not move goal spellings (issues/import-order-moves-goal-spelling.md) or the cost of every laid record's module.

## Done when

A laid record declared with no further call is `Copy` at its codec and has its exact clone, the word map keeps its own, and `lib/_tests/lang/facts/copy_tests.hthr`'s `Header` drops its `generate laid_copy` line.

## What it assumes from elsewhere

- **[[ownership-copy-clone]]** owns the classes and `laid_copy`. Assumed here: only that `laid_copy`'s three values are what a record needs.
