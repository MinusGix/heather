---
title: omega stops at a projection of a projection of a call
status: open
labels: [omega,proofs,elaboration,ergonomics]
area: tactics
created: 2026-10-14
updated: 2026-10-14
---

omega reads a field of a call that unfolds to a constructor
([[omega-unfolds-defined-propositions]]), but not a field of such a field:

```text
import pos; import rat; import omega;
theorem b(n: Nat): Pos(n).int() = OfNat(n) + OfNat(1) { omega }                 -- ok
theorem a(n: Nat): Rat::inv_succ(n).den.int() = OfNat(n) + OfNat(1) { omega }   -- stuck
theorem c(n: Nat): Rat::inv_succ(n).den.pred = n { omega }                      -- stuck
```

The stuck runs list `rat::Rat::inv_succ(n).den.pred` as an atom.
`Rat::inv_succ(n)` is `Rat(OfNat(1), Pos(n))`, so `.den` is `Pos(n)` and
`.pred` is `n`; the reader unfolds one projection and stops.

Workaround (`Rat::inv_succ_half`, lib/std/rat.hthr): state the denominator
with `refl` in a typed `let`.

Wanted: when the inner projection's receiver whnfs to a constructor, keep
reducing the outer projection, bounded like the other probes. Acceptance:
both probes above check, and the `refl` restatements in `inv_succ_half`
go away.

## What it assumes from elsewhere

- **[[omega-unfolds-defined-propositions]]** owns the one-level read.

## Log

- 2026-10-14: The repro's shape is gone with the shifted Pos ([[retire-shifted-pos]]): Rat::inv_succ(n).den is Succ(n), one projection, and both 'Rat::inv_succ(n).den.int() = OfNat(n) + OfNat(1)' and 'Rat::inv_succ(n).den = Succ(n)' now check by omega. A projection of a projection of a call is still unread in general; a new repro needs a record field holding a record. inv_succ_half keeps its refl lets because ring, not omega, consumes them (ring reads Nat::int(Succ(..)) as an atom).
