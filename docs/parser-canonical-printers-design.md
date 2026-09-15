# Optional canonical printers for parsers

Design proposal; not an implemented API. Owner:
[parser-canonical-printers](../issues/parser-canonical-printers.md).

## Primary contract

A printer should be indexed by the particular parser it is certified against.
In schematic notation:

```text
Prints(p : Parser<T,A>) {
    print : A -> List<T>
    round_trip : (a : A) -> run(complete(p), print(a)) = Ok(a)
}
```

This asks the printer to choose one accepted representation for each value.
It does not require unique input spellings or recovery of the original input.
For a parser that normalizes number spellings, the printer can choose the
canonical spelling. Different formatting policies can supply different
explicit dictionaries for the same parser.

A restricted printer takes `Printable(a)` evidence. A parser cannot print all
of `A` if some values in `A` have no accepted representation. Where the result
contains relevant proofs or uses a quotient-like observation, specify the
observation/equivalence explicitly rather than assuming proof irrelevance or
silently weakening equality.

## Composition needs boundaries

Whole-input round trips alone are insufficient for sequencing. Printing the
digits `12` and appending `3` can cause a greedy number parser to read `123`.
The reusable stronger contract therefore needs permitted suffixes, framing,
or delimiter evidence:

```text
Boundary(a, suffix) ->
    observe(p on print(a) ++ suffix)
      = success(a, length(print(a)))
```

The exact law must also account for source context if the parser can inspect
its whole source or starting offset. A start-of-source law must not silently
be generalized to every cursor. A source-span law can quantify a prefix,
the printed fragment, a permitted suffix, and the cursor at their boundary.

Useful combinator rules would include:

- **Recognition:** select a token which the supplied selector maps to the
  requested value, with a proof of that equation.
- **Map:** for `f : A -> B`, require a section `choose : B -> A` with
  `f(choose(b)) = b`. Then print `choose(b)`. `f` need not be injective;
  unreachable values require a restricted domain.
- **Sequencing:** prove that the second printed component satisfies the first
  parser's boundary contract and that both preserve the intended source span.
- **Dependent bind:** print the first value, then the payload whose type
  depends on it. A length-prefixed format can carry its length proof directly.
- **Choice:** the selected branch's round trip is not sufficient when an
  earlier branch can accept the same tokens with a different value. Require
  branch compatibility, or prove the round trip for the combined choice.
- **Repetition:** require item boundary/separation evidence; consumption alone
  only establishes progress, not unambiguous segmentation.

These are optional capabilities with explicit evidence. Arbitrary parser
functions and arbitrary post-processing do not automatically acquire a
printer.

## Two different round trips

1. Parsing a printed value recovers that value.
2. Printing parsed tokens may normalize their spelling.

The first is the proposed primary law. Exact recovery of original token
spelling needs additional retained information and its own theorem.

The calculator's grammar soundness theorem connects successful recognition to
an independent derivation. A canonical printer must additionally connect its
generated tokens to **successful recognition by the executable parser**.
Producing a derivation alone does not establish that direction.

## First prototype

Start with a selected token, framed sequencing, a many-to-one map with a
chosen section, and a dependent length-prefixed format. Include refusal tests
for a wrong printer, a false section, greedy suffix absorption, and choice
interference. Use these examples to decide whether one class with stronger
optional laws or separate whole-value/framed dictionaries gives the cleaner
interface.

## Calculator example

A first calculator printer can parenthesize every binary expression. For
`Plus(Plus(Lit(1),Lit(2)),Lit(3))`, it emits the tokens for `((1+2)+3)`.
That preserves the supplied AST even though unparenthesized sums parse with
right association. Many parenthesizations parse to the same AST; the printer
chooses one. A later printer can minimize parentheses using the grammar's
precedence levels without changing the primary round-trip requirement.
