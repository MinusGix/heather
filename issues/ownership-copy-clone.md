---
title: Copy, Clone and the exact-clone extension, derived from a layout
status: open
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
