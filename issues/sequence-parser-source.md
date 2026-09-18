---
title: A scannerless String calculator, over an abstract parser source
status: open
labels: [stdlib,parser,showcase,design,elaboration]
created: 2026-09-18
updated: 2026-09-18
---

The calculator showcase parses a `List<PTok>` that someone else produced.
Nothing in the pipeline starts from text, so `String` — which landed as a
specification type in [[string-char-spec-types]] — has no consumer, and the
parser library's deliberate "no string lexer" non-goal (`docs/parser-library.md`)
has never been tested against an actual character grammar.

Two decisions, taken in discussion 2026-09-18, recorded in
`docs/sequence-parser-source-design.md`:

1. **The calculator becomes scannerless**: a `Char` grammar, not a lexer
   feeding the token grammar. A `Number` derivation carries its *digits*, so
   `spelling` is the digit characters and `meaning` is the decimal fold —
   there is no `Nat`-to-decimal rendering function and no render/parse
   round-trip theorem anywhere. Whitespace is carried in the derivation
   (a `spacing` field whose `WellFormed` obligation is that every character
   is a space), so the span theorem still says the derivation spells the
   source character for character.
2. **The parser library's source becomes abstract**: a `Sequence<S, T>` class
   over a `SeqOps<S, T>` operations record, replacing the hardwired
   `List<T>`. `List<A>` and `String` are the two instances. A grammar fixes
   its token type in the constraint and stays polymorphic in the source, so
   one calculator runs on a `String` and on a `List<Char>`.

## What the probes settled (2026-09-18, `probes/str`)

Measured against the tree at 3d10b94 with a freshly built release binary
(the one on disk predated the literal support and rejected `"…"`):

- The parser library already runs at `T = Char` with no changes at all:
  `run(p, s.chars)` type-checks and `run_string(some(digit), "123") = Ok([1,2,3])`
  holds by `refl`. Character classification by `nat::leb` on codes and
  `digit_val` by subtraction are all `refl`-decidable and cheap.
- A record field cannot quantify over a constrained type parameter, so a
  token-indexed `Parser<T, A>` whose `run` field is source-polymorphic
  (rank 2) is **not expressible**; genericity has to live in the function
  signatures instead, which is where the library already keeps it.
- A two-parameter class is required: with the element type as an associated
  field (`class Seq<S> { Elem: Type, … }`) a grammar cannot say "my element
  type is `PTok`". `<S: Sequence<PTok>>` says it, and resolution has no hole
  because the source argument determines `S`.
- A record's type parameters cannot carry a constraint, so the operations
  travel as an **index parameter** — `finite_set`'s `SetOperations`/`FiniteSets`
  pattern. An instance index must be a bare global reference (`string_ops`,
  not `string_ops()`).
- The whole shape checks and reduces: `Cursor<S, T>(ops, source)` with
  `within: Le(offset, ops.seq_len(source))`, a token-fixed source-polymorphic
  consumer, and `refl` equations at **both** `String` and `List<Char>`.

## Cost

The parser library is 1082 lines over seven modules with 128 signature sites
mentioning the source; each gains an `S` parameter and the operations index,
and the cursor laws restate through `ops.view`. Eight records gain an index.
This is the expensive half of the issue and it buys the generality the
scannerless calculator demonstrates.

## Plan

- Round 1: character classification in `lib/std/char.hthr` — `is_digit`,
  `is_space`, `digit_val` and their soundness lemmas.
- Round 2: certified repetition in the parser library. `many`/`some` carry a
  `Consumes` certificate but **no `Post`/span contract**, so a proof-carrying
  multi-digit numeral has nothing to lean on. This is the first consumer to
  need spans that concatenate, so the library gains the contract rather than
  the showcase routing around it.
- Round 3: the scannerless calculator over `List<Char>`, with the derivation
  carrying digits and spacing. This is the consumer, and it lands before the
  abstraction so that the class interface is chosen against a real client
  rather than guessed.
- Round 4: `lib/std/sequence.hthr` — `SeqOps`, the `Sequence` law class, the
  `List` and `String` instances, and the drop lemmas at the view.
- Round 5: migrate the parser library onto the abstract source, and re-point
  the calculator at `S = String`.

## Log

- 2026-09-18: Rounds 1–3 landed; the design record is `docs/sequence-parser-source-design.md`.

  - `lib/std/char.hthr`: `is_digit`, `is_space`, `code_is`, `digit_val`,
    `digit_of`, and the facts around them — `selected_of_match` (the inversion at
    an abstract `Bool`, because a `match` on the computed class does not refine
    `digit_of(c)`), `digit_selected`, `digit_val_lt`, `code_is_sound`,
    `code_is_char`.
  - `lib/std/list.hthr`: `cong_append_r`, the missing counterpart of
    `cong_append_l`.
  - `docs/showcase/calc_text.hthr`: the scannerless calculator. `Number` carries
    its digits, whitespace is carried per-lexeme with an all-spaces obligation,
    and the spelling is a **difference list** (`spell(d, tail)`), so no
    `append_assoc` or `append_nil` appears anywhere — each production's span
    proof is one congruence under `spell(d, ·)`, where the token version needs a
    three-way `span_join`. Whole-input soundness is `parse_sound`, and the
    compiler agreement is proved at an open parse result as `calc_parser` does.
  - Fifteen `refl` equations, all green first try: `calculate("7")`,
    `calculate("407")` (multi-digit), precedence, product-before-sum, sum
    association, `calculate("(2+3)*4")`, `calculate(" 2 + 3 * 4 ")`,
    `calculate(" ( 2 + 3 ) * 4 ")`, `execute("2+3*4") = Ok(Some([14]))`, and five
    error cases (`""`, `"2+"`, `"(2"`, `"2 3"`, `"+2"`).

  **The showcase is not wired into the suite.** It needs more than 8 GiB cold —
  it passes at 20 GiB and dies at the 6 GiB per-process rail `scripts/test` sets
  — so it is not in `crates/elab/tests/showcase_calculator.rs` beside
  `calc_parser` yet. The cause is measured and is not the grammar: a record token
  type costs 27× an inductive one's conversion misses in a controlled pair
  (`probes/str/p10.hthr`), logged on
  [[elaborator-canonical-type-spelling]] with the numbers. Wiring it in waits on
  that defect; two spellings were tried against it and neither is the lever.

  Filed on the way: [[parser-certified-repetition]] — `many`/`some` carry a
  consumption bound but no span contract, so the digit run is hand-rolled as
  `checked_run`, which is that contract at one relation in twenty lines.

  Rounds 4–5 (`lib/std/sequence.hthr` and the migration of the parser library
  onto it) are unstarted. The design doc §2 records what the probes settled about
  the shape, including two things that constrain it: a record field cannot
  quantify over a constrained type parameter (so no rank-2 `run`), and an
  associated element type cannot express "my tokens are `PTok`" (so the class
  takes two parameters and the operations travel as an index, `finite_set`'s
  pattern).
- 2026-09-18: Full `scripts/test` after rounds 1–3: **2802 passed, 0 failed, 5 ignored**. Tracker check clean. `docs/showcase/calc_text.hthr` is checked through the CLI, not by the suite, for the rail reason above.
