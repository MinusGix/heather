---
title: A scrutinee named `code` parses as a quotation
status: closed
labels: [frontend,parser,diagnostics]
created: 2026-08-13
updated: 2026-08-16
---

Found writing the showcase (docs/showcase/README.md, friction 1, 2026-08-13): in
`fn run(code: List<Tok>) { match code { ... } }` the parser sees `code {` and
commits to the quotation form `code { … }`, so an ordinary variable named
`code` cannot be matched on (or start any expression a `{` follows). The
error is baffling at the site: ``expected `}` to close the quote`` pointing
at the first match arm.

The quote parse guards only on `Ident("code") + LBrace` (parser.rs, `code {`
lookahead), which is exactly the shape `match <var> {` produces. Options, not
decided here: bind-aware lookahead (a local named `code` in scope wins over
the quote form), a real keyword (breaks the "plain variable named `code`
works everywhere else" property the current lookahead exists to keep), or
keeping the grammar and making the diagnostic name the collision and the
rename that fixes it. Whatever the fix, the diagnostic should stop blaming
the brace.

## Log

- 2026-08-16: LANDED. 'match code { … }' is an ordinary match on an ordinary variable. None of the three options this issue listed was taken, because none was what the code wanted — the framing was one site and it is two, neither needing bind-aware lookahead, a keyword, or a diagnostic-only patch.

Site 1, the quotation arm (parser.rs, primary): the guard gains '&& !self.no_record_lit'. That flag ALREADY means 'a { here belongs to the enclosing form, not to me' — it is what stops 'match x { … }' reading its arms as a record literal — and the quote arm simply was not consulting it. Note what this issue's own text got wrong: match_expr's intensional-form guard was already correct and had already, deliberately, declined to read 'match code {' as the analysis form; the commit to the quotation happened one level DOWN, in the ordinary expression parser reached for the scrutinee.

Site 2, found by the round's own test failing rather than by the report: the same gap one form up. 'match code as λ z => Nat { … }' took the 'match code e as T' path and died with 'a match code needs its result type' — nth(1) was 'as', not '{', so the existing guard let it through. The guard now declines on 'as' beside '{'.

The rule that unifies them, and the reason declining costs the analysis form nothing: '{' and 'as' are exactly the follow tokens that CANNOT BEGIN AN EXPRESSION, so there was never a scrutinee they could have been. The escape hatch is the one no_record_lit already documents for record literals, and it needed no new machinery: a bracket lifts the restriction, so a quotation that really is the scrutinee is parenthesised — 'match (code { 0 }) { … }', pinned as ExprKind::Quote.

RESIDUE, and deliberately not decided here: a follow token that CAN begin an expression still reads as the analysis form. 'match code (x) as T' is the live one — a call to a function named 'code' in scrutinee position is unreachable without parens on the whole scrutinee. That is a genuine ambiguity between two real forms rather than a gap, so it wants a decision and not a lookahead tweak; filing it is the right move if a second customer appears. The showcase's customer is served: its parameter is matched on directly.

Tests +3 in crates/syntax/src/parser.rs: a_scrutinee_named_code_is_an_ordinary_variable (scrutinee asserted Var("code") with both arms, plus the motive form that found site 2), a_quotation_still_parses_where_the_brace_is_its_own (the control that the fix took ONLY the scrutinee — quote as a block result, in a let, as an argument, plus the parenthesised scrutinee asserted still a Quote), and the_intensional_match_is_untouched (the analysis form parses; its missing-motive diagnostic is unchanged). Verified end to end through the CLI: the reported repro went from 'expected } to close the quote' to 'ok'. docs/showcase/README.md friction 1 marked resolved, with the wider finding. Suite 1646 -> 1649, full run on the final tree.
