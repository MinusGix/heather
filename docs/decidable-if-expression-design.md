# Decidable `if` expressions

## Decision

Heather's source `if` branches on a proposition with a `Decide` instance:

```heather
if a <= b { b } else { a }

if h : P {
    // h : P
    yes(h)
} else {
    // h : P -> False
    no(h)
}
```

The condition is a type-level proposition `P`, not a `Bool`. There is no
implicit `Bool`-to-proposition coercion; Boolean case analysis remains an
ordinary constructor match. This keeps specification-level branching aligned
with the existing `Decide<P>` abstraction instead of exposing its `P ∨ ¬P`
representation at each call site.

`if` is a true grammar keyword and therefore cannot be used as a binding
name. Both branches are braced blocks, so local `let` statements are available
without introducing another branch-body syntax.

## Lowering and evidence

The parser lowers

```heather
if h : P { yes } else { no }
```

to the same match tree as

```heather
match decide<P>() {
    Inl(h) => yes,
    Inr(h) => no,
}
```

The two occurrences of `h` inhabit separate scopes and have types `P` and
`P -> False`, respectively. The form without a binder uses unspellable
internal names. `MatchForm::If` is retained only as source provenance for
diagnostics; computation and dependent elimination continue through the
ordinary `Or` match implementation.

Normal implicit resolution supplies `Decide<P>`. Consequently an explicit
local dictionary takes precedence in exactly the same way it does for a
direct call to `decide<P>()`. A failed search is reported at the `if` and
prints the written condition rather than the parser-generated call.

## Checking and inference

In a checking position the lowered match uses the existing dependent motive
synthesis. Branches can therefore establish results whose indices follow the
actual `Inl` or `Inr` decision, rather than being restricted to choosing two
values of a non-dependent type.

An `if` can also infer a constant result type. Elaboration tries a branch in
its proper evidence context, then accepts the inferred type only when it can
be strengthened back into the surrounding context without that evidence. It
checks both branches against that outer type. This supports direct expression
use and unannotated `let` bindings while preventing a branch-local proof from
escaping its scope. A genuinely evidence-dependent result still needs an
expected type, just as an otherwise ambiguous dependent match does.

## Standard-library use

`Int::max` and `Int::min` are the initial representative users:

```heather
fn max(a, b: Int) -> Int { if a <= b { b } else { a } }
fn min(a, b: Int) -> Int { if a <= b { a } else { b } }
```

Their `Decide<Le(a,b)>` instance is declared before these definitions because
Heather resolves declarations in source order.

## Boundaries

- This feature says nothing about efficient runtime compilation of arbitrary
  proofs; that remains the `Compile`/representation boundary.
- `if let`, `let else`, and pattern conditions are separate language designs.
- The syntax deliberately requires `else`; proposition branching has two
  evidence-producing cases and neither is silently discarded.

## Verification contract

Focused tests cover closed Nat decisions, equivalence with explicit matching,
both evidence types, dependent proofs, local dictionaries, block bodies,
constant-type inference, missing-instance diagnostics, and rejection of raw
`Bool` conditions. The Int library tests cover the representative standard-
library migration.
