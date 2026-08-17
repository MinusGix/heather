---
title: An equation has no head, so Decide<n = m> cannot be an instance
status: open
labels: [frontend,elaboration,traits,design,stdlib]
created: 2026-08-17
updated: 2026-08-17
---

An instance is keyed on its carrier's head name (`{Head}::{Class}`), and an
equation has none. `instance Decide<2 = 2>` reports

    the carrier `2 = 2` has no head type name, so this instance has no
    canonical name (docs/traits-layer1-design.md §4.1)

and the 2026-08-17 carrier widening ([[decide-class]],
`docs/decide-class-design.md` §2) deliberately did **not** answer for
`TyKind::Eq` while it was widening `head_name` for everything else.

## Why it was left out rather than swept in

One reserved head — `Eq` — would be one key for equality at *every* type, so
`Decide<n = m>` at `Nat` and `Decide<b = c>` at `Bool` would collide as
duplicate declarations. Keying it correctly needs the **endpoints' type** in the
key, and that is the (class, carrier-syntax) key `docs/traits-layer1-design.md`
§7.1 defers to layer 2 and §8 lists as residue.

So this is the one place in the `Decide` round where the deferred layer-2 key
is genuinely the blocker, rather than the thing a reader would wrongly assume
is blocking (§2.2 of the design doc records that resolution never consults the
head at all, so the key blocks naming and duplicate detection only).

## The cost today

`std/nat`'s `eq_dec` is an ordinary `fn`, called by name. That is not painful —
every consumer in the library calls it directly anyway — so this is a
completeness item rather than a blocked customer. The customer appears when
something wants `Decide<P>` where `P` is *built* from an equation: a decided
`Mem` on lists needs elementwise equality, and [[std-api-waves]] L3 is where
that lands.

## What it assumes from elsewhere

- The key itself is layer 2's canonical-derivation table
  (`docs/traits-design.md` §12's content-addressed minting, which is already
  keyed on (class, carrier-syntax) by design).
- [[value-generic-instances]] is independent: that one is about *binders*, this
  one is about the *key*, and an equation carrier would want both — `n = m` at
  open `n`, `m` is exactly a value-generic instance.

## Acceptance

`instance Decide<n = m>` at `Nat` registers and does not collide with an
equality instance at another type; `eq_dec` fills it; and a goal at a composed
proposition mentioning an equation resolves.
