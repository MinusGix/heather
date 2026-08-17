---
title: "Type-argument speculation was exponential once both sites could recover"
status: closed
labels: [frontend,syntax,parser,performance]
created: 2026-08-16
updated: 2026-08-16
---

`fn f(h: A<A<A<…<Nat) -> Nat { 0 }` — an unterminated type-argument chain —
took **4.7 s at depth 20 and 7 ms at depth 10**, a clean 4× per two levels.
The expression spelling `a<a<a<…<b` did the same. Both were introduced by
[[nat-order-kit]]'s `<`-in-type-position fix the same day, and both are fixed
here.

## The mechanism, which is the part worth keeping

Two sites speculate on a `<`: `Parser::try_tyargs` in the expression grammar
(there since [[surface-polymorphism]]) and the `D<A, B>` branch of
`Parser::ty` (added by the `Lt` round). Each falls back by **rewinding and
re-parsing the same tokens the other way**.

`docs/surface-polymorphism.md` §1 said "backtracking is free here — the parser
is a `Vec<Tok>` plus an index — and it is total, so no lookahead heuristic can
be wrong about a program". Every clause of that is true, and the conclusion was
still only accidentally safe: it held because the *type* side **failed hard**,
which cut the recursion at the first level. Making that side recover removed
the cut, and two mutually-re-entrant recovering speculations are exponential by
construction — each level re-parses every prefix below it, twice.

So this is not "backtracking is expensive". It is: **speculation is free only
while failure is terminal**, and the moment a second site starts recovering,
the pair needs a memo. That is the sentence the parser now carries.

## The fix

Packrat memoization of **failures only**, over the one nonterminal that needs
it: `Parser::spec_failed: HashSet<(usize, u8)>`, checked before either site
speculates and inserted on either site's failure. Linear, and measured flat to
depth 120 in both spellings.

Three things the key had to get right:

- **The site is part of the key.** The expression site requires a closing `>`
  where the type site's caller may accept other continuations, so one position
  can fail for one site and succeed for the other.
- **The parser's four mode flags are part of the key** — `no_record_lit`,
  `no_eq`, `no_iff`, `motive_body` — because `ty()` reaches the expression
  grammar, where all four change what parses. Without them the memo would
  answer a question it was not asked.
- **Failures only.** A success consumes its tokens and is never retried, so
  there is nothing to memo on that side; and memoizing the two *reinterpretation*
  rewinds (the `(`-follows and connective-follows discriminators, where the
  type-argument parse **succeeded** and is then re-read) would be wrong, since
  those are not failures at all. Measured flat regardless.

## What this does not fix

Nothing about which programs parse — [[comparison-inside-type-arguments]] is
still the residue it was, and the memo is asserted not to move that boundary.
The deeper question of whether `<…>` should exist at all is
[[retire-angle-bracket-type-arguments]]; if that lands, this memo and both
speculating sites are deleted rather than maintained.

## Log

- 2026-08-16: Found, fixed and closed in one round. Found by asking whether the
  landing round's own fix was the right shape rather than by a failure —
  "backtracking is free here" was a claim in a design doc, and it was measured
  instead of believed. +2 parser tests: a depth-200 termination check (a cost
  test written at a depth the exponential cannot survive, so it needs no timing
  and no threshold) and an acceptance test pinning that the memo moves no
  boundary.
