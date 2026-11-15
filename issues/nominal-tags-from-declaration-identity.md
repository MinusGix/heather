---
title: Derive nominal tags from the declaration, not from how many inductives came before it
status: closed
labels: [elaboration,inductives,caching]
area: infrastructure
created: 2026-10-26
updated: 2026-10-30
---

An inductive's nominal tag is the count of inductives the elaborator
committed before it (`Types::commit`, `crates/elab/src/types.rs`), and every
constructor carries it in its kernel type (`inductive::tag_type`). So what a
module elaborates to depends on how many inductives its process loaded
before it, not only on what it imports:

- The same module checked by two processes with different prefixes is two
  elaborations with different kernel terms. That is why the library gate's
  folders could not share images until they all loaded one canonical
  prefix (`docs/archive/library-world-design.md`), and why that world still makes a
  process replay shared modules it does not need: loading only its own
  closure would move the tags.
- An inductive added upstream moves every later tag, so everything after it
  is a different elaboration. No registry granularity in the early cutoff
  ([[early-cutoff-registry-and-order-granularity]]) can move an image across
  that edit; the refusal "the world's registries differ" is correct today.

Derive the tag from the declaration instead: a hash of the qualified name
(`module::Name`, and the shape declaration's for an `IWf` route), refused
with a located error on a collision with any committed tag rather than
probed onward (probing would make it order-dependent again). Reserved tags
(`COLLECTION_LITERAL_TAG`) stay reserved. Then a module's kernel terms are a
function of its closure up to Ψ positions, which the early cutoff already
remaps.

## Acceptance

- Inventory every reader of `next_tag` and of tag order (anything assuming a
  later declaration has a larger tag), and every place a tag is predicted
  before its commit (`inductive.rs`, the `IWf` skeleton).
- Collisions refused with both declarations named; a negative test that
  forces one.
- A test that one module elaborates to the same image over two prefixes that
  differ by an unrelated inductive.
- Measure what a larger tag literal costs conversion
  ([[nominal-tag-conversion-cost]] found the tag was most of a comparison
  once).

## What it assumes from elsewhere

- **`docs/archive/library-world-design.md`** §4: this is the first of the two
  changes that would let a process load only its closure; the second is
  the early cutoff observing only what the closure contributes.

## Log

- 2026-10-30: Done on [[module-dag-build]]: `types::declaration_tag` hashes `module::Name` (the IWf shape is `D#shape`), a collision is refused naming both (`a_tag_collision_is_refused_naming_both`), and `next_tag` is gone; the image format version is bumped. A tag is a compact `NatLit` either way, so its magnitude costs conversion nothing (`docs/module-dag-design.md` §3).
