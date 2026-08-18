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

> **Amended 2026-08-17** (see the log): that key landed, in a cheaper form than
> this paragraph assumed — the registry key is a tuple of *resolved declaration
> references* (`docs/instance-resolved-key-design.md`), with no layer-2 table
> involved. The endpoints' type in the key is now an ordinary carrier
> component, so this half is paid. What is left is the canonical **name** for a
> headless carrier, and the UX.

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
  open `n`, `m` is exactly a value-generic instance. **Landed 2026-08-17**, and
  the independence held exactly: it moved this issue not at all. The binder half
  is now free — `instance(n, m: Nat) Decide<n = m>` would bind its two values —
  and what still refuses is `head_name` at `TyKind::Eq`, which is this issue and
  nothing else.

## Acceptance

`instance Decide<n = m>` at `Nat` registers and does not collide with an
equality instance at another type; `eq_dec` fills it; and a goal at a composed
proposition mentioning an equation resolves.

## Log

- 2026-08-17: Second customer, and the sharpest so far (wave L3, [[std-list-mem-and-perm]], 2026-08-17): this key is what splits the two halves of one algorithm's specification. `Mem` needs only `=`, so it is polymorphic and lives in `std/list`; `count` must DECIDE `a = h`, so `decide<a = h>()` finds no instance, `nat::eq_dec` is called by name, and `count` is at `Nat` — a permanent monomorphic hole in an otherwise polymorphic list API. The dictionary-passing spelling (decider as a parameter, threaded through every call site) works and was deliberately NOT written, per the push's no-encoding-around doctrine. Ranked #2 of that round: fewest lines, largest design consequence.
- 2026-08-17: The new-key half of this issue is PAID, and the cost estimate drops accordingly. `docs/instance-resolved-key-design.md` (2026-08-17) rebuilt the instance registry's key as a tuple of RESOLVED declaration references — (class key, carrier-head key, index spelling), no component a spelling — which is the cheap form of the (class, carrier-syntax) key `docs/traits-layer1-design.md` §7.1/§8 deferred to layer 2. It needed no canonical-derivation table: the enabling step was noticing that a *key* never had to be spellable, only a *name* did. So the sentence above — 'keying it correctly needs the endpoints' type in the key, and that is the (class, carrier-syntax) key deferred to layer 2' — no longer describes a blocker. There is no new notion of key to invent and no layer-2 table to wait for. What remains is: (1) a carrier component for `TyKind::Eq` — the endpoints' type as a resolved reference, which is what every other carrier component already is, so `Decide<n = m>` at Nat and at Bool land at different keys by construction; (2) the canonical NAME, which is the part that does still want a decision, since `Eq` is not a declared head and `{Head}::{Class}` has nothing to build from (identity and naming came apart in that round — §4 — so this is now a naming question in isolation, and a minted unwritable name is available where it was not before); (3) the UX — writing the instance, and the diagnostics. Estimate: from 'blocked on a layer-2 table nobody has designed' to a bounded slice, most of it (2) and (3). Still NOT implemented here, deliberately: that round's brief scoped it out and there is no evidence in it about the equation case.
