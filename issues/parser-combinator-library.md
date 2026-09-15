---
title: Build a parser combinator library with checked consumption and progress
status: closed
labels: [stdlib,parsing,proofs,design,ergonomics]
created: 2026-09-14
updated: 2026-09-15
---

## User direction and sequencing

2026-09-14: build a proper parser combinator library. Remainder and progress
tracking belong to that library's design. Improve the elaborator foundations
listed in `blocked-by` before implementing the library so its ordinary source
can use the improved basics. Do not schedule a separate remainder-API round
as an intermediate deliverable. The roadmap owns ordering among these tasks.

## Design scope

Use the checked calculator as the first real grammar. Design a small generic
parser interface over token streams with value mapping, sequencing/bind,
choice, token recognition, optional parsing, repetition, and end-of-input
checking. Establish how recursive grammars compose with termination checking.

The consumption model should tie a remainder to its input, not only bound its
length. A suffix relation and compositional evidence are a candidate design,
not a frozen representation. Distinguish zero-or-more consumption from strict
progress: optional parsers may succeed without consuming, while repetition
must not loop on empty success. Composition, rebasing, and mapping should
preserve evidence without clients spelling transitivity arithmetic.

Choose and document failure/choice semantics: consumed versus unconsumed
failure, commitment/backtracking, retained input position, and useful errors.
Choose how progress is expressed (types, witnesses, or an equally checked
contract) and how nullable parsers interact with `many`. No accepted recursive
or repetition path may depend on an unchecked termination claim.

## Acceptance

- A generic open token/value client and the calculator both use the library.
  Rewrite the calculator with numbers, precedence, the existing right
  association, parentheses, complete-input checking, and explicit errors.
- Establish reusable laws for remainder identity/composition, value mapping,
  and strict progress as required by the chosen design. Parser clients avoid
  hand-written `le_trans`/`le_succ_r` plumbing for ordinary sequencing.
- Check empty input, nullable success, repeated consumption, nested parsing,
  chosen backtracking/commitment behavior, and error positions/priority.
- Refuse invalid consumption/progress evidence; empty-success repetition
  must be statically refused or handled by an explicitly specified total
  behavior, never silently diverge.
- Preserve the calculator's checked AST examples and open-input compilation
  agreement theorem, with false grammar/result controls in the suite.
- Inspect elaboration cost and proof-term growth for composition and nested
  parsing before committing to a broadly reused representation.

## Boundary

Text/character literals and a character lexer are useful future clients,
not prerequisites for this generic token-parser library. No custom parser
syntax, native runtime representation, or general grammar completeness theorem
is automatically required by this issue. File any required residue explicitly
before closing its chosen implementation scope.

## What it assumes from elsewhere

- **[[result-map-receiver-dispatch]]**: receiver calls select compatible operations.
- **[[callback-expected-type-propagation]]**: available expected result types
  reach checking-only callback bodies.
- **[[typed-termination-obligations]]**: inferred dependent locals can enter
  correctly scoped decrease obligations.
- **[[termination-local-evidence]]**: available progress proofs can discharge
  recursive-call obligations without ordinal manual glue.
- **[[stable-termination-obligation-names]]**: necessary manual proofs have
  stable source handles.
- **[[showcase-token-parser]]**: the checked calculator provides the baseline
  grammar behavior and compilation law.

## Log

- 2026-09-14: All scheduled elaborator foundations are complete, including
  [[stable-termination-obligation-names]]. The library is now ready to start.
- 2026-09-14: User requests a design round before implementation, explicitly
  exploiting dependent types for composition and behavioral proofs. Proposal:
  `docs/parser-combinator-library-design.md` — source-indexed cursors,
  intrinsic forward movement, parser-indexed progress and semantic
  certificates, dependent bind, explicit commitment/backtracking semantics,
  pointwise observational laws, and guarded recursive builders. Signatures
  remain schematic pending checked representation/composition prototypes;
  no combinator API has been implemented or frozen by this design round.
- 2026-09-14: Implemented the first checked prototype in
  `docs/showcase/parser_core.hthr`, with dependent bind, observation laws,
  derived/cached cursor coherence, token recognition and a guarded recursive
  client. Negative testing found that offset/bound fields alone erased source
  distinctions between equal-length inputs; an explicit source-endpoint
  equality field preserves the intended distinction. Details and boundaries:
  `docs/parser-core-prototype.md`. The full library issue remains open.
- 2026-09-14: Prototype acceptance: focused **2 passed** (checked source laws
  plus seven negative controls); full `scripts/test`: **2668 passed, 0 failed,
  5 ignored**. Tracker and whitespace checks pass.
- 2026-09-14: Implemented `lib/std/parser.hthr` and migrated the calculator.
  The library includes dependent composition, operation-indexed progress and
  source-span soundness certificates, committed ordered choice/backtracking,
  diagnostics, lookahead, optional/finite/unbounded repetition, and guarded
  recursive grammar helpers. Map and bind laws include observable failures
  and commitment. Generic clients, false-certificate controls, axiom audits,
  the calculator's prior examples/compiler theorem, and a nested cost sweep
  pass focused acceptance (**6 passed**). API and measured bounds:
  `docs/parser-library.md`.
- 2026-09-14: Scoped follow-ups are explicit: [[parser-grammar-soundness]] owns
  an independent calculator grammar relation and its additional theorem;
  [[parser-cached-cursor-cost]] owns a cached representation comparison. The
  initial library does not claim full grammar completeness or linear runtime.
- 2026-09-14: Final full `scripts/test`: **2673 passed, 0 failed, 5 ignored**.
  Tracker and whitespace checks pass. The initial library acceptance is
  complete; remaining broader grammar/performance work is separately owned.

- 2026-09-15: [[parser-grammar-soundness]] supplies the independent calculator theorem and extends the certificate bridge; current API details are in `docs/parser-library.md`.
- 2026-09-15: The component layout needs an umbrella import; explicit declaration-preserving reexports are tracked by [[module-reexports]].
- 2026-09-15: 2026-09-15: umbrella restored — `import parser;` is the whole library via reexports ([[module-reexports]] closed); components remain importable with the same identities.
