---
title: Tag types are built from the same formers as lowerings, so structural guards can mistake one for the other
status: open
labels: [elaboration,inductives,representation]
area: language
created: 2026-09-06
updated: 2026-09-06
---

Found by [[inductive-spelling-codes-nonrecursive]]'s round (2026-09-06). A
declaration's nominal tag type (`tag_type`, `crates/elab/src/inductive.rs`)
is a right-nested Σ of `Unit`s — the binary digits of the tag. A nullary
constructor's payload is `Σ(tag_type(D)). Unit`, and for the declaration
with tag 0 that is `Σ(Unit). Unit`: structurally the digit-1 component of
every later declaration's tag type. A scan-based guard that compared a
sub-type against registered payloads spelled the tag types inside every
later lowering as `El (Bool#payload₀^δ)` — convertible, unreadable by
`tag_of`, 81 test failures — and was replaced by a positional guard.

The hazard is general. Every gendef guard is "can only decline" *because
lowerings are assumed distinctive*, and the whole-type guard
(`ty_type_ref`) has the same latent collision: a fieldless
single-constructor declaration at tag 0 would lower to `Σ(Unit). Unit`
whole, and every later tag type's digit-1 would respell to it. Nothing
prevents that today except the prelude's first declaration not being
that shape.

## Fix shapes

1. Make tag types unmistakable: a former no lowering produces at that
   position (an `Empty`-based digit, or a marker Σ head), so no payload,
   suffix or whole lowering is ever `==` to a tag component. Touches every
   reader of `tag_type`/`read_tag`, and the nominal-separation tests.
2. Or make the walkers structural about *position*: `respell_deep_at`
   skips a Σ's first component (always the tag) and never descends into a
   tag type at all. Cheaper; leaves the whole-type collision at tag 0.
3. Either way, a test: declare a fieldless single-constructor type first
   (tag 0) and elaborate a monomorphized instance beside it.

## What it assumes from elsewhere

- **[[elaborator-canonical-type-spelling]]** owns the guards' doctrine.
  Assumed here: only that guards compare structurally against lowerings.
- **[[inductive-spelling-codes-nonrecursive]]** owns the positional
  guard that avoided this. Assumed here: only that `respell_ty` no longer
  scans.

## When

Triggered: the next guard that names anything below a whole declaration,
or the first user library whose first declaration is fieldless.
