---
title: Connect a checked token parser to the calculator compiler showcase
status: closed
labels: [frontend,stdlib,proofs,showcase]
created: 2026-09-14
updated: 2026-09-14
---



## Scope

Make `docs/showcase/calc_parser.hthr` parse natural-number tokens, addition,
multiplication, and parentheses into the existing calculator's `Expr`.
Connect it to direct evaluation and the proved RPN compiler, check the realized
showcase in the ordinary suite, and update the gap table.

Character lexing, shell IO, native compilation, and a general grammar
soundness/completeness theorem are outside this slice.

## Implementation

Three adjacent `decreases list_len(ts)` declarations implement the idealized
parser's right-associated grammar. The crucial extra information is
`Parsed(limit)`: an expression, a remaining token list, and a proof that its
length is at most `limit`. `tail_bound` transports that proof along a match
equation after an operator or closing parenthesis is recognized. The two
returned-tail recursive calls cite the resulting `small` proof explicitly;
the forward calls and the parenthesis back edge use the existing closer.
No compiler or kernel changes were needed.

The surface needs explicit annotations on the successful parse result, the
remaining list, and the strict-decrease proof so the existing obligation
lifter can give its helpers closed signatures. `parse_atom` uses nested
matches on the list and its token: a deep pattern on that recursion parameter
is deliberately refused by the existing guard. These are checked spellings,
not new inference machinery.

`compile_result_correct` proves the pipeline law at an open
`Result<Expr, ParseError>`; `parsed_compile_correct` specializes it to
`parse(ts)` for an arbitrary token stream. This uses the existing
`compile_correct` theorem and needs no unfolding equation for the mutual
group. The result map is explicitly qualified and instantiated because the
combined imports also expose other operations named `map`.

## Acceptance

- AST equations for both precedence directions, both operator associations,
  parentheses, and nested parentheses with an open numeric payload.
- Kernel computations for direct evaluation and RPN execution (`14`, or `20`
  with parentheses changing precedence).
- Explicit errors for empty input, missing operands, leading/doubled
  operators, empty/missing/wrong parentheses, trailing input, and first-error
  priority; an execution error propagates unchanged.
- The ordinary acceptance test checks both `calc.hthr` and `calc_parser.hthr`.
  Five independent false-theorem controls must fail with the kernel's
  `NotConvertible`, not an import or inference failure.

## What it assumes from elsewhere

- **[[result-propagation]]** owns function-scoped `Result` propagation.
  Assumed here: it composes with the existing measure lowering.
- **[[mutual-recursion-declarations]]** owns adjacent mutual groups.
  Assumed here: forward rank calls and explicitly proved decreasing back
  edges share a checked recursion.
- **[[group-unfolding-equations]]** owns mutual unfolding companions.
  This client does not require them; proofs are factored through an open
  parse result.

## Log

- 2026-09-14: Implemented the parser and pipeline law. Focused acceptance:
  `scripts/test --fast -p heather-elab --test showcase_calculator`, 1 passed;
  full `scripts/test`: **2641 passed, 0 failed, 5 ignored**. Standalone
  `heather check` with caching disabled also passes for `calc_parser.hthr`
  and its imported calculator. `scripts/issue check` and `git diff --check`
  pass. The scoped acceptance is complete.

- 2026-09-14: [[result-map-receiver-dispatch]] replaces qualified map calls
  in the pipeline laws with receiver syntax; callback inference remains
  owned by [[callback-expected-type-propagation]].
- 2026-09-14: [[typed-termination-obligations]] removes local parse-result
  annotations and allows direct field matches while preserving acceptance.
- 2026-09-14: [[termination-local-evidence]] removes both ordinal decrease discharges; existing local progress proofs are selected automatically.
- 2026-09-14: Migrated the grammar to [[parser-combinator-library]] while preserving all AST/error examples and the open-input compiler agreement theorem. [[parser-grammar-soundness]] owns the independent grammar proof.
