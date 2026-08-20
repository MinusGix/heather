# Equality as an instance carrier

## Decision

An instance whose carrier is an identity type is registered by the resolved
nominal carrier of its endpoints:

```heather
instance(n, m: Nat) Decide<n = m> { dec := eq_dec(n)(m) }
instance(a, b: Bool) Decide<a = b> { dec := eq_dec(a, b) }
```

The two instances coexist because their keys contain `Nat` and `bool::Bool`,
respectively. Resolution continues to try the complete generated instance
value against the goal `Decide<lhs = rhs>`; the key is registration identity
and duplicate detection, not an approximation used for type checking.

## Structural key and generated name

An equation has no declared surface head. Inventing one global `Eq` head would
collapse equality at every endpoint type, while keying it directly as `Nat`
would collide with an ordinary `Decide<Nat>` instance. The carrier component
is therefore:

```text
Eq(resolved endpoint carrier)
```

Internally this is encoded with an unspellable `#Eq@` prefix followed by the
existing resolved carrier key. The prefix cannot be introduced by source and
the suffix is a declaration identity, so neither component is a user spelling.

The generated value lives under the endpoint type's real namespace with an
unspellable equality suffix, for example `Nat::Decide#Eq`. This lets the normal
instance assembler emit ordinary declarations without pretending equality is
a declared type or exposing a canonical name users should call. Source reaches
the value through resolution:

```heather
decide<n = m>()
if n = m { yes } else { no }
```

## Finding the endpoint carrier

Instance value binders are in scope in the carrier:

```heather
instance(n, m: Nat) Decide<n = m> { ... }
```

Registration builds the same telescope prefix as a generated instance
declaration—type parameters followed by value parameters—and elaborates the
identity type there. The lowered `Id` explicitly contains the common endpoint
type. Reading its nominal carrier uses the same `carrier_of_ty` path as
operator and member dispatch, so module qualification and kernel `Nat` follow
existing rules.

Function types and other structurally non-nominal endpoint types are refused
with a targeted message. A local dictionary remains usable at such a goal;
this round defines global registration only where there is a stable resolved
owner.

## Binder and termination walks

Equality is not opaque to instance analysis. Both endpoint expressions are
walked by:

- recoverability checking, so `n` and `m` are recognized as determined by the
  goal `Decide<n = m>`;
- Paterson size and occurrence checks, so an equality-headed instance cannot
  hide a non-decreasing recursive requirement.

This was a necessary part of the feature: registration initially reached the
new key but rejected every useful value-generic equality instance because its
binders appeared absent.

## Standard library and boundaries

`std/nat` registers its existing recursive `eq_dec`; `std/bool` adds the
four-case constructor decision and registers it independently. The instances
compute, drive proposition-directed `if`, and backchain through connective
instances such as `Decide<(n = m) ∨ False>`.

This does not assert that every type has decidable equality. An unregistered
nominal type still produces the ordinary missing-instance trace, and equality
at an abstract or non-nominal carrier needs an explicit dictionary or a future
carrier-level equality class.

## Verification contract

Tests pin registration at two endpoint carriers, coexistence with an ordinary
instance at `Nat`, direct and composed resolution, both computed `if` branches,
the absence of accidental fallback for an unrelated inductive, the
non-nominal refusal, and the instance binder walks.
