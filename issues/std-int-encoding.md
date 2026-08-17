---
title: "Int: the encoding choice, and the arithmetic/order kit it costs"
status: open
labels: [stdlib,design,proofs,performance]
blocked-by: [nat-order-kit]
created: 2026-08-16
updated: 2026-08-16
---

There is no `Int`. This issue owns the encoding decision and the kit that
follows from it. It is deliberately **after** the `Nat` and `List` waves
([[std-api-waves]]): it is the first library file whose proof burden is not
three-line induction, so it is worth reaching with the order kit already in
hand.

## The encoding

Recommendation: **`inductive Int { OfNat(n: Nat), NegSucc(n: Nat) }`** — the
Lean encoding, reading `NegSucc(n)` as `-(n+1)`.

Why: every integer has exactly one representation, so structural equality *is*
equality, `absurd` and constructor no-confusion keep working unchanged, and no
quotient type is needed.

The rivals and why they lose:

- **Difference pairs `Nat × Nat` quotiented by `(a,b) ~ (c,d) ⟺ a+d = c+b`** —
  mathematically the prettiest, and it needs quotients, which do not exist
  ([[setoid-auto-lifting]] is the substitute and is a much larger commitment
  than an encoding choice).
- **Sign plus magnitude** (`Neg(Nat) | Zero | Pos(Nat)`, or a `Bool` sign
  field) — two representations of zero in the naive spelling, junk values, and
  every lemma pays for them.
- **Binary/two's complement** — a *runtime representation*, which is
  [[datarepr-separation]]'s business, not the spec type's. It should arrive as
  a `Compile` instance over the canonical form, not replace it.

## What it costs, which is the point

`Int::add` is a four-way split whose mixed-sign cases route through `Nat`'s
`sub` and a comparison, so `add_comm` and `add_assoc` are **not** three-line
inductions — they are case analyses with a `sub` lemma at the bottom of each.
That is why the file is worth writing:

1. It is the best available **realistic checking-speed workload** — proof
   volume from a real development shape rather than from a benchmark fixture.
2. It measures how much the absence of [[grind-port]] / an `omega` actually
   hurts, on the arithmetic where such a tactic earns its keep.
3. It cashes `Nat`'s `sub` kit, which [[nat-order-kit]] adds and which nothing
   else in the library currently stresses.

Under Prop-first the order story is *cheaper* here than it would have been:
one relation stated once, rather than a `leb`-shaped pair per sign case.

## Sketch of the kit

`neg`, `add`, `sub`, `mul`; `add_comm`/`add_assoc`/`add_zero`/`add_neg`
(making it the first `Group` instance the algebra module could carry — worth
checking whether `Group` should exist before this lands);
`mul_comm`/`mul_assoc`/`mul_one`/distributivity; `Le`/`Lt` and their kit;
`ofNat`/`toNat` and the embedding lemmas connecting them to the `Nat` kit.

## What it assumes from elsewhere

- **[[nat-order-kit]]** owns `Nat`'s order and `sub`. Assumed here: only that
  the `sub` cancellation lemmas exist, since the mixed-sign cases are stated
  in them.
- **[[datarepr-separation]]** owns runtime representations. Assumed here: only
  that a machine-integer representation is its business and not an argument
  about the spec encoding.
- **[[std-api-waves]]** owns sequencing. Assumed here: only that this comes
  after the `Nat`/`List` waves.

## Log

- 2026-08-16: Filed out of the std-API design discussion, with the encoding
  recommendation recorded rather than left implicit — the point being that
  the choice is forced by "no quotients" plus "no junk values", so it can be
  settled now even though the round is not scheduled.
