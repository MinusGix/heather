---
title: Discharge closed facts through fast Decide instances rather than by reducing the specification
status: open
labels: [stdlib,elaboration,decidability,performance,design]
created: 2026-09-07
updated: 2026-09-07
---

Proof by reflection — prove `decide(P) = True → P` once and let the kernel
check the decision procedure's run instead of reducing the specification —
is the library-side answer to closed facts whose natural spelling is too
large to reduce ([[kernel-acceleration-policy]]). The objection is that it
introduces a second notion: proofs want to talk about `unsigned_lt`, the
specification, and reflection seems to make them talk about
`unsigned_lt_bit`. This issue is the design that keeps one notion at proof
sites, and the sketches below are its shape.

## What already exists

- `class Decide<P> { dec: P ∨ ¬P }` in `lib/std/logic.hthr`
  ([[decide-class]]), instances keyed at type formers and value-generic
  (`instance(n, m: Nat) Decide<Le(n, m)>`), `decide<P>()` and
  `decide_pick`. A closed `P` is already discharged by evaluating `P.dec`
  and matching `Inl(h) => h`; what is naive is the *procedure* the derived
  instance runs (`Le` on `Nat` peels).
- The BitVec module already pairs each executable bit with its
  proposition through an iff: `carry_add_bit_true_iff`,
  `borrow_sub_bit_true_iff`, used as `….mpr(h)`. Those bridges are the
  reflection theorems; they are just not registered anywhere.

## The design: the instance *is* the fast procedure

The specification stays the notion. What changes is which procedure the
`Decide` instance for it runs:

```
// the notion proofs use — unchanged
fn unsigned_lt(n: Nat, a, b: BitVec(n)) → Type { toNat(n, a) < toNat(n, b) }

// the width-bounded decision, and the bridge proved once by induction
fn unsigned_lt_bit(n: Nat, a, b: BitVec(n)) → Bool { borrow_sub_bit(n, a, b) }
theorem unsigned_lt_reflects(n: Nat, a, b: BitVec(n)):
    (unsigned_lt_bit(n, a, b) = True) ↔ unsigned_lt(n, a, b) { … }

// the instance: decide by the bit, transport by the bridge
instance(n: Nat, a, b: BitVec(n)) Decide<unsigned_lt(n, a, b)> {
    dec := match unsigned_lt_bit(n, a, b) as λ c => (unsigned_lt_bit(n, a, b) = c) → … {
        True  => λ h => Inl(unsigned_lt_reflects(n, a, b).mp(h)),
        False => λ h => Inr(λ p => bool::no_confusion(trans(sym(h), unsigned_lt_reflects(n, a, b).mpr(p)))),
    }(refl)
}

// a closed fact at machine width: the statement is the specification
theorem boundary(): unsigned_lt(64, ofNat(64, 0), ofNat(64, 9223372036854775808)) { decide }
```

`decide` here is the existing `decide<P>()` narrowed to `Inl`: the
elaborator evaluates the instance's `dec` (the kernel reduces
`unsigned_lt_bit`, width-bounded) and takes the left injection, refusing
with the ordinary `NotConvertible` when it is `Inr`. Nothing about
`unsigned_lt_bit` appears in the theorem or in any lemma that consumes it;
the second notion exists once, in the instance. Instance resolution is what
picks the fast procedure over the derived one, so registering a faster
decision later is a library change with no proof churn.

Two refinements the sketch needs:

- **A `decide` goal combinator** (`crates/elab/src/goal_combinators.rs`): at
  a closed goal `P` with a `Decide<P>` instance in scope, elaborate
  `or_left(P.dec)` — a fixed term, so the kernel's verdict is the whole
  trust story. `trivial` could try it as a last resort so that closed ALU
  facts read `{ trivial }` as the `carry(4)` examples already do.
- **Ordering of instances.** The derived `Decide<Le(m, n)>` on `Nat` and a
  fast instance for `unsigned_lt` do not overlap (different heads), but
  `toInt`-based `signed_lt` and a bit-based instance would; the resolution
  order needs the more specific (BitVec-headed) instance to win, which
  [[decidable-relations-and-comparison]] should settle together with the
  `Cmp` question.

## Beyond decision: certificates

For relations that are only semidecidable, or whose decision is itself
large, the same shape works with a **witness** found outside the kernel and
checked inside by a small reduction — reflection with an untrusted search:

```
// Nat order at magnitude: the witness is the difference, `+` on runs is one program
theorem lt_of_diff(a, d, b: Nat, h: a + Succ(d) = b): a < b { … }
theorem big(): 5 < 9223372036854775808 { lt_of_diff(5, 9223372036854775802, _, refl) }

// reals (regular Cauchy, [[regular-cauchy-reals]]): `x < y` is Σ n. y(n) − x(n) > 2·2^-n;
// the elaborator searches n, the kernel checks one rational inequality at that n
theorem apart(): lt(x, y) { exists_intro(n := 12, decide) }
```

The rational inequality at the witness is again a `Decide` instance over
normalized pairs, so reals reduce to rationals reduce to `Int` bits. This
is where [[shared-arithmetic-reflection]]'s typed atoms and checked
coefficients belong: a solver emits the witness and the certificate, the
kernel reduces only the certificate.

## Acceptance

- `Decide` instances for `unsigned_lt`/`unsigned_le`/`signed_lt`/`signed_le`
  on `BitVec` backed by the executable bits and their iffs; the width-64
  boundary facts of [[bitvec-closed-reduction-cost]]'s rail restated as
  specifications and discharged by `decide` under ordinary fuel.
- A `decide` combinator (or `trivial` fallback) with a refusal control: a
  false closed specification is refused, and the refusal names the
  instance.
- A note in `docs/decide-class-design.md` on instance ordering, or a pointer
  to [[decidable-relations-and-comparison]] where it is settled.

## What it assumes from elsewhere

- **[[decide-class]]** (closed) supplies the class and value-generic
  instances.
- **[[decidable-relations-and-comparison]]** owns the `DecidableRel`/`Cmp`
  factoring and instance precedence.
- **[[bitvec-width-bounded-defaults]]** makes the executable bits cheap
  over computed operands; without it the fast instance is fast only over
  literals.
- **[[shared-arithmetic-reflection]]** and the reals issues
  ([[regular-cauchy-reals]], [[positive-naturals-and-rationals]]) are the
  certificate customers.
