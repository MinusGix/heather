# Calculator grammar soundness

The specification and implementation live in `docs/showcase/calc_parser.hthr`.
The specification does not call the parser to decide grammar membership.

## Independent productions

```text
expression := factor | factor '+' expression
factor     := atom   | atom '*' factor
atom       := number | '(' expression ')'
```

`Derivation` is a syntax tree for these productions. `AtomFactor` and
`FactorExpr` explicitly embed one precedence level in the next. `WellFormed`
checks the levels of the children: a sum's left child is a factor, whereas
its right child is an expression. Thus an unparenthesized left-associated sum
cannot masquerade as the specified right-associated production. Products
similarly require an atom on the left and a factor on the right.

`spelling` reconstructs tokens, including parentheses. `meaning` removes the
production embeddings and parentheses to produce the calculator's `Expr`.
These are structural functions on derivations, independent of recognition.

`Grammar(level, source, begin, end, value)` contains a derivation, its
well-formedness, its precedence level, and two equalities:

```text
meaning(derivation) = value
rest(source, begin) = spelling(derivation) ++ rest(source, end)
```

The second equality connects the recognized prefix to the actual source and
remaining suffix. `WholeGrammar(source,value)` instead requires
`spelling(derivation) = source`.

## Constructing the evidence

The recursive implementation returns `Certified` successes, whose value,
end cursor, forward proof and evidence are direct fields. Production bodies
combine recognition evidence and recursive child derivations. The recursion
itself receives a callback that requires a strict decrease in remaining input;
same-position precedence calls use the existing mutual-recursion ranks.

`forget_at` projects an ordinary parser reply. Its `forget_post` theorem
exposes the stored evidence through the ordinary `Sound` interface. This
avoids needing an external unfolding theorem for a mutual recursive group,
which the current elaborator does not generate. It does not postulate a
recursive equation or define the specification by running the implementation.

Library additions support this pattern:

- `recognized_head` connects a selected token with the exact remaining suffix.
- `certified_map_at` transforms a certified value and its postcondition.
- `certified_finish_at` combines mapping and cursor rebasing with a proved
  forgetting law. The calculator uses concrete sum/product finishing helpers
  to keep its larger dependent types cheaper to check.
- `result::fold` eliminates success/failure generically; using it and
  `and_then` avoids repeatedly generating concrete nested Result eliminators.
- `complete_sound` preserves a postcondition and adds an empty final remainder.

The public `parse` signature and calculator AST/error constructors stay the
same. Evidence is internal to the parser result projected by that entry point.
No general proof erasure or proof irrelevance is assumed. Token-recognition
failures are retryable by construction; optional operators and the number/open
alternative use that property. Consumed recursive and closing-token failures
retain commitment and diagnostic merging.

## The public theorem

```heather
theorem parse_sound(source: List<PTok>, value: Expr,
    success: parse(source) = Ok(value)):
    WholeGrammar(source,value)
```

This is success soundness on an arbitrary source, not just example evaluation.
`expression_sound` also exposes the prefix theorem from an arbitrary valid
starting cursor. The three precedence-level certificates retain their own
relations before completion.

Soundness does not promise success on every well-formed derivation. General
ordered-recognition completeness remains a separate decision. The canonical
printer follow-up must prove that the actual parser accepts its chosen
spellings; using a valid grammar derivation alone would not prove that law.

## Remaining API work

Proof construction currently exposes more cursor and equality plumbing than
ordinary parser composition. `issues/parser-certificate-ergonomics.md` owns
improving that interface using this client. `issues/parser-canonical-printers.md`
owns optional printing and its round-trip contracts. Cursor caching and its
proof/checking costs remain with `issues/parser-cached-cursor-cost.md`.

## Checking cost

The first nested certificate/composition version exceeded the 6 GiB test rail.
The flatter record, generic Result elimination and separate production helpers
fit that rail, but checking this proof remains expensive. Acceptance uses a
serial gate. [The checking-cost issue](../../issues/parser-certified-composition-cost.md)
owns profiling and reducing the cost; it is distinct from rescanning input
prefixes. No source/cache performance guarantee follows from this proof.

## Validation

Focused parser/calculator acceptance: **5 passed, 0 failed**. It checks the
normal complete module, independent witnesses with an open numeral and suffix,
open source/cursor success implications, malformed span/AST/production refusals,
all prior calculator equations and false-result controls, and depths 1/2/4/8.
Axiom reports for the recursive implementation, public theorems and supporting
library laws are empty. The depth cases reuse the already checked calculator
image; no case was removed when consolidating the fixtures.

Full `scripts/test`: **2672 passed, 0 failed, 5 ignored** (2026-09-15).
Tracker and whitespace checks pass.
