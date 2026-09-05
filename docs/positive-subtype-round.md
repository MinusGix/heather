# Positive numbers: an operation with one extra obligation

A positive natural is a number together with evidence that it is positive.
The [checked example](showcase/positive_subtype.hthr) starts with an ordinary
record:

```heather
record PositiveNat { value: Nat, valid: 0 < value }
```

`.value` is explicit. The evidence field here is an ordinary relevant proof.
This gives us a concrete customer for lifting before choosing construction
sugar or a default evidence policy for future subtype syntax.

## Adding two positive numbers

The arithmetic already exists. The extra obligation is that its result stays
positive:

```heather
fn positive_add(x, y: PositiveNat) → PositiveNat {
    PositiveNat(
        value := x.value + y.value,
        valid := add_positive(x.value, y.value, x.valid))
}
```

`add_positive(n, m, positive)` proves `0 < n + m` from `0 < n`.
The ambient lemma is slightly stronger than this wrapper needs: the second
number can be any natural. The wrapper supplies the required hypothesis from
its first input. Projecting the result's `.value` computes to the original
addition, and the example checks that computation with `refl`.

If the closure lemma is missing, write an ordinary proof goal in that field:

```heather
fn add_missing(x, y: PositiveNat) → PositiveNat {
    PositiveNat(value := x.value + y.value, valid := ?valid)
    on ?valid := add_positive(x.value, y.value, x.valid);
}
```

Without the `on` clause the declaration remains incomplete. The goal has the
inputs in scope and asks for positivity of their sum. The printer preserves
`x.value` and `y.value`; arithmetic currently uses the resolved names `Lt`
and `add` in this diagnostic. Supplying that proof
completes the same declaration. Supplying just `x.valid` fails: positivity of
one input is a hypothesis for the closure lemma, not the result's condition.

## Using the laws we already proved

For this algebra, two positive numbers are equivalent when their values are
equal:

```heather
fn SameValue(x, y: PositiveNat) → Type { x.value = y.value }
```

The stored proofs do not occur in this relation. Associativity transfers by
applying the existing arithmetic theorem to the values:

```heather
theorem positive_add_assoc(x, y, z: PositiveNat):
    SameValue(positive_add(positive_add(x, y), z),
        positive_add(x, positive_add(y, z)))
{ add_assoc(x.value, y.value, z.value) }
```

The record's computation rules make this proof fit. No comparison of the
closure proofs is needed. Compatibility of addition is also checked, so the
example registers `Semigroup<PositiveNat>(SameValue, positive_add)`.

The relation-indexed `Semigroup` in `algebra_rel` composes equivalence,
operation compatibility, and associativity. `Mergeable` now extends this
composition with commutativity and idempotence. The older identity-based
`algebra::Semigroup` remains a separate interface.

The showcase's generic `reassociate_inside` theorem uses `rel_cong` and the
semigroup laws. After explicitly designating `+` as `positive_add` and `≈` as
`SameValue` at this carrier, its client reads:

```heather
theorem group_positive_sum(a, b, c, d: PositiveNat):
    ((a + b) + c) + d ≈ (a + (b + c)) + d
{ reassociate_inside(a, b, c, d) }
```

Once the addition wrapper exists, a caller can also write:

```heather
fn twice(x: PositiveNat) → PositiveNat { x + x }
```

The positivity proof is reused through the operation; the caller owes no new
closure lemma.

The expected conclusion in `group_positive_sum` supplies the relation and
operation, as in the finite-set example. This `+` calls the certified subtype wrapper; `.value`
remains explicit when the programmer wants an ambient natural number.

## Why zero fails

Trying to construct the usual additive identity exposes the problem directly:

```heather
fn zero_unit() → PositiveNat {
    PositiveNat(value := 0, valid := ?valid)
}
```

The required evidence is `0 < 0`, which the goal display reduces to `False`.
The showcase proves its negation using
`lt_irrefl(0)`, and the tests reject an attempted `trivial` proof. The failure
is already at construction: zero cannot be proposed as an element of this
subtype.

## What this round establishes

This is a checked manual wrapper and law transfer. Expected-result wrapper
insertion, closure-lemma discovery, and general law generation remain in
[subtype-transfer-and-evidence](../issues/subtype-transfer-and-evidence.md).

The example proves `SameValue(PositiveNat(n, p), PositiveNat(n, q))` for
arbitrary valid evidence `p` and `q`. A regression rejects using `refl` to
assert identity of those whole records. Comparing values therefore does not
silently identify their stored proofs.

The squashed-condition syntax proposed in
[the three small experiences](three-small-transfer-experiences.md) remains a
separate policy candidate. Its wrapper would use squash-preserving combinators.
The broader comparison of relevant proofs, squashed proofs, and evidence reuse
still belongs to the parent issue.

The display fix in this round recognizes the registered projections used by
this dependent record. [Inline record projection display](../issues/inline-record-projection-display.md)
tracks the remaining diagnostic gap for other record layouts and generic
records.
