---
title: A formatter for Heather source
status: open
labels: [tooling,syntax,ergonomics]
created: 2026-09-16
updated: 2026-09-16
---



## Problem

Parts of the library are written in a visibly different hand from the rest —
`pure_at(source,begin,value)`, `fn map_at<T,A,B>` — and nothing checks the
difference. The damage is not spread evenly, which decides the shape of the
answer:

| | `,` not followed by a space |
|---|---|
| `lib/std/parser/*` (7 files) | 1,741 |
| everything else under `lib/` | 49 |
| `examples/` | 0 |

97 % of it is one subtree. A general pretty-printer would rewrite all 22 k
lines of `.hthr` to repair six files.

## Shape: a token-stream normalizer, not an AST pretty-printer

The formatter re-emits the **token stream** with canonical spacing and never
moves a line break. Three properties decide this over a printer:

1. **The safety check is total and mechanical.** `lex(fmt(src))` must equal
   `lex(src)` kind-for-kind. Heather's lexer is adjacency-sensitive — `?p` is
   the named hole and `? p` is an anonymous hole applied to `p`; `nat::sub`
   joins only when adjacent; `·₂`, `$x`, `¬P` likewise — so a whitespace edit
   *can* change meaning. Token equality rules that out wholesale, without
   anyone enumerating the hazards. The printer's analogue
   (`parse ∘ print ∘ parse == parse`, span-insensitive) needs a total printer
   over the parser's grammar and span-insensitive equality over the AST: more
   work for a weaker guarantee.
2. **Comments cost nothing.** The lexer drops them, but every `Tok` carries a
   span, so `src[prev.span.end .. next.span.start]` *is* the trivia. Only the
   whitespace inside that gap is normalized; comment text is never touched and
   never moves relative to its neighbours. No attachment policy, no lexer
   change. A printer has to solve comment attachment properly, and that is
   most of its cost.
3. **The cleanup commit is reviewable.** No rule changes a line break, and
   nothing but whitespace changes, so the one-time reformat shows up under
   `git diff -w` as nothing but the blank lines it collapsed.

It does **not** reflow: the 76 over-100-column lines in
`parser_combinators.hthr` stay as written until phase 3.

The formatter must run on source that does not elaborate. That rules out
expressing it as lints, even though `LintFix { span, replacement }` already
exists (`crates/elab/src/diagnostics.rs:93`) and nothing currently applies one:
`crates/elab/src/lint.rs` runs a lint "after its owning item has elaborated
successfully", and code is most in need of formatting when it is broken. Home
is `crates/syntax` — the lexer and the source text are the whole dependency.

## The one thing tokens cannot decide

`TokKind::Lt` is emitted for both the comparison operator and the opener of a
type-argument list; `Vec<T, A>` wants tight delimiters and `a < b` wants pad.
`TokKind::Gt` is unambiguous (`>` is never an operator), but bracket-matching
back to an opener is unsound, because comparisons appear *inside* argument
lists — `Decide<a <= b>`.

Resolved by the spike below: derive the openers from the AST and treat the
remaining `Lt` as operators. When the file does not parse, leave `<`/`>`
spacing alone and normalize everything else — degrade, never refuse.

**Build this as a general token-role table, not a `<` special case.** `<` is
the only ambiguous token *today* — `-` is prefix-only, the infix table carries
`Star` but no `Minus` — but [[infix-subtraction-notation]] is open and would
make `a - b` vs `-b` the second instance of exactly this shape. A span-keyed
`TokenRole` side-table derived from the AST absorbs that at no extra cost; a
`<`-shaped hack would have to be rewritten to.

The spacing table itself is **not** a fourth copy of the operator inventory
(cf. [[machine-readable-syntax-manifest]]): the formatter reads a token stream,
so it needs a classification of `TokKind` into prefix/infix/delimiter, not a
table of spellings. That is one match over the lexer's own vocabulary, living
beside the lexer.

## Rule set (phase 1)

- `,` `;` — one space after when the next token is on the same line, never
  before;
- no padding inside `( ) [ ] ⟨ ⟩` and inside a generic `< >`;
- one space around infix `+ * ++ = ≠ ∧ ∨ ↔ ≈ ⊔ ∙ && || -> => ⊢ :=` and around
  `<` in its comparison role only;
- `:` — space after, none before;
- tight prefixes `¬ - $`, where the lexer's adjacency rules *are* the
  specification — but only when the trivia is **pure whitespace** (`¬ // why\n P`
  keeps its gap, or the comment is swallowed) and only where the token really
  is a prefix operator (see the role table);
- **not** `λ`, which the design first listed here in error: the library writes
  `λ source begin =>` in every occurrence;
- strip trailing whitespace, collapse runs of blank lines, one final newline.

The formatter decides **whether** there is a space, never **how many**. A run
of spaces is the author aligning a column — `tm_lam(dom, b)            =>` and
27 others across four library files — and re-deciding that is not formatting.
This replaces the design's original "collapse runs of spaces to one", which
would have destroyed every aligned block in the library.

Adopt `heather_emit.rs`'s `LINE_WIDTH = 96` rather than inventing a second
width, so generated and hand-written source do not disagree forever.

What the lex-equality invariant does **not** buy: `⟨a |⟩` and `⟨a | ⟩` lex
identically, so taste-level rules need golden fixtures. Safety is mechanical;
taste is tested by hand, and the two must stay visibly separate in the tests.

## Phases

1. `crates/syntax/src/fmt.rs`, `heather fmt [--check]`, `scripts/fmt`.
2. AST-guided **indentation only** — leading whitespace from nesting depth,
   never moving a break. Cannot violate the invariant: a line break already
   separates tokens.
3. Real reflow. Needs the total printer and comment attachment; gate it behind
   demand rather than building it now.

Roll out as [[stdlib-surface-style-lint]] already chose: warning-only against a
baseline, gating in `scripts/test` once `lib/` is clean.

## Acceptance

- `lex(fmt(x))` equals `lex(x)` kind-for-kind over every `.hthr` in the repo;
- `fmt(fmt(x)) == fmt(x)`;
- `fmt` changes no line break in phase 1, and the library reformat is empty
  under `git diff -w`;
- adversarial fixtures for the adjacency forms (`? p` vs `?p`, `·₂`, `$x`,
  `¬P`, `⟨a |⟩`, three-segment qualified names), each with a negative control;
- a file that fails to parse is still formatted, minus `<`/`>` spacing;
- phase 1 retires the `TightNegationSpacing` lint and adopts its two controls
  as formatter fixtures — the exact empty replacement, and the comment between
  operator and operand that must survive.

## Spike: recovering the role of `<` from the AST — done, succeeded

`crates/syntax/tests/generic_delimiter_roles.rs`. Every `>` closes exactly one
argument list, which makes a completeness check free: walk the AST, derive one
`(open, close)` pair per list, and require the derived closers to be exactly
the file's `Gt` tokens.

Over `lib/`, `examples/` and the crates' fixtures — 82 files, 0 unparseable:

```
2858 `>` all accounted for; 2968 `<` = 2858 openers + 110 comparisons;
271 argument lists exist only after desugaring
```

No `>` is claimed by two different openers, and every derived opener is a real
`Lt`. The derivation is therefore complete, and the design is unblocked: the
remaining 110 `Lt` are comparisons.

Three findings the spike produced, each of which would have been a defect:

- **The closer is the *first* `>` after the last argument, not the last `>` in
  the node's region.** A declaration's span covers its whole body, so the
  obvious "last `>` inside the node" walks past the parameter list and claims a
  `>` from the body. This alone accounted for 44 of the 45 initially failing
  files.
- **Parser-desugared nodes carry arguments the author never wrote.** `P ∨ Q`,
  `¬P` and `a = b` reach the AST as `Named { args }` with no delimiters in the
  source — 271 occurrences. "Argument-bearing node" does not imply "has
  delimiters"; the formatter must tolerate this rather than assume. Same
  provenance boundary [[stdlib-surface-style-lint]] already owns.
- **A grouped binder is visited once per name.** `before, after:
  MachineState<Mem>` gives each name its own `Param` over one written `Ty`, so
  the traversal yields the same delimiters twice. Harmless for identical
  edits, a real hazard for anything that counts spans — so the check
  distinguishes a duplicate pair from two openers claiming one `>`.

Sites that need delimiters derived, for the implementation: `TyKind::Named`,
`Squash<A>` (but not `∥A∥`), `Type<n>`, `ClassRef`, `ExprKind::TyApp`,
`RecordLit`, `Decl::tyvars`, `InstanceDecl::tyvars`, and three sites whose
names are bare `String`s with no spans — `class C<A>`, `inductive I<A>`, and
`designation<A>`.

## What it assumes from elsewhere

- **[[surface-syntax]]** owns the grammar. This issue owns the written form of
  landed syntax and never becomes a second specification of it.
- **[[machine-readable-syntax-manifest]]** owns the exported lexical
  inventories. Assumed here: only that operator spelling and fixity acquire one
  authority, so the formatter's infix table is not a fourth copy. The
  Tree-sitter `indents.scm` is a separate, unchecked indentation authority and
  becomes that issue's problem at phase 2, not this one's.
- **[[infix-subtraction-notation]]** would add the second token whose role its
  kind does not determine. Assumed here: only that the role table is built
  general enough to take it, which costs nothing now and a rewrite later.
- **[[stdlib-surface-style-lint]]** owns *which spelling* is idiomatic
  (`f(a, b)` over `f(a)(b)`, operator over named call). This issue owns
  whitespace only and decides nothing about spelling.
- **[[lint-tight-negation-spacing]]** landed the same whitespace rule as a
  lint, and is **subsumed** by this issue (user decision, 2026-09-16). The
  formatter is the single authority for whitespace; phase 1 removes the lint
  rather than leaving two owners to drift. Its value does not vanish — the two
  cases it got right become fixtures here, above.
- **[[fmt-not-enforced-decision]]** is about *Rust* and rustfmt, and does not
  transfer: it turned on a formatter that reformats aggressively against a
  large existing tree, which is exactly what the no-line-breaks rule avoids
  here.

## Log

- 2026-09-16: **Phase 1 landed.** `crates/syntax/src/fmt.rs` (the normalizer)
  and `src/roles.rs` (the role table), `heather fmt [--check]`, `scripts/fmt`,
  a `repository_sources_are_formatted` gate in the ordinary suite, and the
  library reformat: 17 of 63 files, 431 insertions and 446 deletions, every
  deleted line under `git diff -w` a blank one. `TightNegationSpacing` is gone,
  its rule and both its controls now living in the formatter.

  Four things the design got wrong, each found by running it rather than by
  reasoning about it:

  - **`λ` is not a tight prefix.** The library writes `λ source begin =>` in
    every occurrence. Listed in the rule set from the start; nothing but the
    corpus said otherwise.
  - **"Collapse runs of spaces to one" would have destroyed deliberate column
    alignment** — 27 sites across four files. Replaced by the sharper rule that
    the formatter decides presence, never width.
  - **A declared operator symbol is not a prefix operator.** `designation
    prefix - at Int := neg` became `-at`. Both spellings lex identically, so no
    invariant catches it; it needed `TokenRole::OperatorName`, which is the
    second customer of the general role table and vindicates building one.
  - **The generated certificate module had to be formatted at its source.**
    `lib/function_ir_certificates.hthr` is written by a test that also asserts
    it is current, so formatting it in place would have failed on the next
    regeneration. The generator now emits through `format_source`, which is the
    same "generated and hand-written source must not disagree" point the
    original design made about `LINE_WIDTH`.

  Two further findings belong to the derivation rather than the rules. The
  census was passing against a **copy** of the walker left in its own test
  while `roles.rs` shipped a different one; the test now calls the library, as
  it should have from the start. And it was passing over a real bug —
  `instance<…> Decide<¬P>` derived the *instance's* `<` against the class
  reference's `>` — because the check required no `>` to be claimed twice but
  never the mirror. Both directions are checked now, and the opener is the
  nearest `<` to the left of the first argument rather than the first one
  inside the node's span.

  Not done, by design: no reflow. The over-100-column lines in
  `parser_combinators.hthr` are untouched, and the user has confirmed that is
  acceptable. Phase 2 (indentation only) remains unscheduled.

- 2026-09-16: [[lint-tight-negation-spacing]] is subsumed rather than kept
  alongside (user decision). Recorded as an acceptance item: phase 1 removes
  the lint and inherits its controls, so the rule survives as a mechanical
  guarantee instead of a warning.
- 2026-09-16: Filed with the design and the census. The `<`-role spike ran
  first, because it was the one result that could have changed the shape:
  it succeeded, and produced the three findings recorded above.
