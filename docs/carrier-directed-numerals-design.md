# Carrier-directed numerals: design record

## Decision

A written numeral is one syntax form, `ExprKind::Num(n)`. It is never an
integer literal and `-n` is never a second literal form: prefix negation remains
an ordinary operator applied to that numeral.

Numerals have two elaboration modes:

1. In inference position they retain the historical `Nat` default and emit the
   historical `Zero`/`Succ` term.
2. In checking position at `A`, after the existing special `Fin` rule and the
   byte-identical `Nat` rule, elaboration resolves `Numeral<A>` and applies its
   `ofNat : Nat -> A` field to the historical natural term.

The standard class is:

```heather
class Numeral<A> {
    ofNat: Nat -> A,
}
```

It is deliberately one embedding operation rather than a class indexed by the
literal value. Heather already has an ordinary `Nat` term for every numeral;
the notation needs a canonical map out of that carrier, not one dictionary per
number. Laws such as preservation of addition belong to each target carrier's
API and are not prerequisites for writing a numeral.

`algebra` supplies the identity instance at `Nat`; `int` supplies `OfNat` at
`Int`. The Nat instance exists for generic `<A: Numeral>` code. Ordinary Nat
source bypasses it so loading `algebra` does not replace every numeral by a
dictionary projection.

## How a carrier reaches a nested numeral

The resolver uses the nearest available bidirectional anchor without replacing
the Nat inference default:

- A checking position supplies the result carrier to an operator whose
  leftmost operand is a numeral. Thus a body expected at `Int` reads `-3` as
  Int negation and `2 + 3` as Int addition before checking their operands.
- With no expected result, the first non-numeral sibling can supply the
  carrier. Thus `let x = 3 + a` infers `Int` when `a : Int`.
- In an equation whose left operator spine begins at a numeral, the right
  endpoint is inferred first and the left is checked at its type. Thus
  `3 = OfNat(3)` and `-3 = NegSucc(2)` are Int equations, while `3 = 3` remains
  a Nat equation.

This is intentionally bounded bidirectionality rather than delayed typeclass
metavariables. A genuinely unanchored `let x = 3` remains `Nat`, preserving the
language's deterministic default and every existing elaborated term.

## Boundaries

- `Fin` numerals remain indices and keep their existing bounds diagnostics.
- The parser and AST contain no negative-numeral form.
- Missing `Numeral<A>` evidence reports the ordinary instance-resolution trace.
- The class is optional at the language level. Before a module imports or
  declares it, non-Nat numerals retain the historical conversion refusal.
- This feature does not promise an efficient runtime representation. As with
  every specification-level class, compilation and data representation remain
  separate concerns.
