---
title: Indent Heather source from its nesting depth
status: open
labels: [tooling,syntax,ergonomics]
area: language
created: 2026-09-16
updated: 2026-09-16
---



## Problem

[[heather-formatter]]'s phase 1 normalizes spacing *within* a line and
deliberately touches nothing else, so a line's leading whitespace is still
whatever its author typed. Continuation lines are the visible cost: a wrapped
signature in `lib/std/parser` is indented by hand, and two adjacent ones need
not agree.

## Scope

Leading whitespace only. Decide each line's indent from the nesting depth of
the token that starts it, and change nothing else — in particular **never move
a line break**, which stays phase 3's business and is currently unowned by
deliberate decision (see the closing log on [[heather-formatter]]).

This cannot violate phase 1's safety invariant, and that is the reason to do it
this way: a line break already separates two tokens, so no edit to the
whitespace between them can change how they lex. The existing
`lex(fmt(src))`-equality and line-structure tests therefore cover this phase
unchanged, and the work is a new rule rather than a new kind of risk.

Most of the machinery exists. `crates/syntax/src/roles.rs` already walks the
AST for delimiter spans; depth per line is the same walk asking a different
question.

## Open questions

- What sets the depth of a *continuation* line — the enclosing delimiter, or
  the construct (a `->` chain in a signature reads differently from an argument
  list)? A rule that indents both the same will look wrong in one of them.
- Blocks written on one line (`fn swap<A, B>(p: Pair<A, B>) → Pair<B, A> {
  Pair(p.snd, p.fst) }`) have no continuation to indent and must be left alone
  rather than exploded.
- Alignment survives phase 1 by the rule that the formatter never decides how
  many spaces there are. An indent rule decides exactly that for column 0, so
  it needs its own answer for a deliberately aligned continuation.

## Acceptance

- Every invariant in `crates/syntax/tests/fmt.rs` still holds, unmodified.
- The reformat is reviewable: report how many lines change and in which files
  before applying, as phase 1 did.
- Cases for a wrapped signature, a wrapped argument list, a one-line block, and
  a deliberately aligned continuation.

## What it assumes from elsewhere

- **[[heather-formatter]]** owns the formatter, its invariants, and the rule
  that no line break moves. Assumed here: only that indentation was left out of
  phase 1 deliberately and not because it is unsafe.

## Log

- 2026-09-16: Filed on closing [[heather-formatter]]'s phase 1, so the deferred
  half has an owner rather than keeping its parent open indefinitely.
