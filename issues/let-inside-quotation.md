---
title: Decide whether a block expression may be a quote payload
status: open
labels: [metaprogramming,frontend,syntax,elaboration]
area: language
created: 2026-08-02
updated: 2026-08-16
---



`docs/let-and-blocks-design.md` §4 made `{ stmt* expr }` an expression in every
prefix position. A `code { … }` payload is one of those positions, so
`code { { let code x = f(g); nth_code($x, i) } }` would *parse* the day that
lands — and its `let`s would elaborate as aliases at `Layer::Code`. §7.2 of
that design declined to answer whether they should, and the implementing round
made the decline real: `atom`'s quote arm rejects a block as the payload's top
level with a message naming this issue, and `quote.rs`'s `scan_splices` gains
an `err` arm rather than a recursive walk, so a block nested deeper inside a
payload is a rejection too.

**Why it was declined rather than allowed.** Two mechanisms would have to be
re-established, neither of which the block round touched:

- **Letbox hoisting.** `scan_splices` collects a payload's distinct `$name`
  term splices in first-occurrence order, and that order *is* the `LetBoxTm`
  nesting order. A `let` inside the payload introduces a second binding
  construct into the same region, and whether a splice under it hoists to the
  same place — or must hoist past a binding that mentions it — is not
  established. The failure mode is a silently mis-hoisted splice, which
  `docs/surface-fin-indexing-design.md` §6 item 10 already flagged as the
  expensive one: it does not fail, it produces the wrong code.
- **The meta-ANF invariant.** [[box-synthesis-gap]] settled how elaborated
  code avoids the box synthesis gap, and `let code` (`Stmt::LetCode`) is the
  surface letbox that respects it. An ordinary `let` at `Layer::Code` inside a
  payload is a *third* thing — neither a letbox nor a program-layer alias —
  and what it means for the payload's context `g` is exactly the question.

**Why it would be useful.** `lib/vec_code.hthr`'s templates are the client:
every `meta fn … for vec.*` payload that wants a shared subterm currently
either repeats it or hoists it to a `let code` above the quote, which is a
different scope and only available for *code*-typed values.

**What a round here has to decide**, in the order the questions bind:

1. Does a payload-level `let` bind at `Layer::Code` or `Layer::Meta`? (The
   parser's `let code x` already spells the second.)
2. Does `scan_splices` walk into a block's statements, and if so, is the
   hoisting order still first-occurrence over the flattened payload?
3. Is the answer different for the payload's *top level* (which the parser
   rejects today) and for a block nested deeper (which `scan_splices` rejects)?

## What it assumes from elsewhere

- **[[in-language-map]]** owns the quotation slice. Assumed here: only that a
  payload is one expression and splices hoist letboxes at the quote boundary.
- **[[box-synthesis-gap]]** owns the meta-ANF invariant. Assumed here: only
  that `let code` is the surface construct that respects it.

## Log

- 2026-08-02: Filed by docs/let-and-blocks-design.md's implementing round (§7.2's recommendation, acceptance item 12). Both rejections are live and tested: the parser declines a block as a quote payload's top level (parser.rs, atom's quote arm) and scan_splices declines a block anywhere inside a payload (quote.rs). Neither is a deferral of effort — the block form itself was cheap; it is a deferral of an ANALYSIS, and the failure mode if it is guessed wrong is a splice that hoists to the wrong place and produces well-typed but wrong code.
- 2026-08-02: Sibling filed, so the two are not confused: [[meta-body-statement-loop]] is a `let` in the `meta fn` body OUTSIDE the quote (it already works unannotated; the meta slice has its own statement loop and rejects an annotated one). This issue is a `let` INSIDE the payload, where the open question is letbox hoisting order rather than which annotations the slice admits.
- 2026-08-13: Adjacent parser finding filed 2026-08-13: [[match-scrutinee-named-code]] — the `code {` quote lookahead also captures an ordinary variable named `code` in scrutinee position (`match code {`), found writing the showcase. Different fix space, same lookahead.
- 2026-08-16: The adjacent finding above is resolved and takes nothing from this issue: [[match-scrutinee-named-code]] landed 2026-08-16 by having the quote arm consult no_record_lit, so the lookahead stands down only where the '{' belongs to the enclosing form (a scrutinee, a motive, a block-preceding type). The quote arm's own refusal of a BLOCK as the payload's top level — this issue's subject — is untouched, and so is scan_splices'. The lookahead is shared; the analysis this issue defers is not.
