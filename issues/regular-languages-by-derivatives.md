---
title: "Regular languages: denotation, Brzozowski derivatives, and a DFA of derivatives proved once"
status: open
labels: [stdlib,mathematics,automata,lexer]
area: mathematics
milestone: [math-formal-languages,self-lexer]
created: 2026-11-10
updated: 2026-11-10
---

Area 5 of the 2026-11-10 ranking. The mathematics under
[[regex-dfa-compiler]], which stays the compiler client.

`lib/std/text/regex.hthr` parses regex syntax. `lib/lang/lexer` holds one
automaton written by hand. Nothing states what language a regex denotes.

## Scope

- Languages over an alphabet as predicates on lists, with the regular
  operations and their laws up to extensional equality.
- `Regex<A>` with its denotation; nullability and the derivative, with
  `w ∈ L(r) ↔ nullable(derive*(r, w))`; a matcher by iterated
  derivatives, correct by that theorem.
- Derivatives modulo similarity (associativity, commutativity and
  idempotence of `+`) are finitely many: the bound that makes the
  reachable set a finite type ([[finite-cardinality-and-pigeonhole]]).
- A DFA as a record over a finite state type with its language;
  the derivative automaton accepts `L(r)`; product and complement.
- Longest-match tokenisation over a list of rules as a specification
  the scanner loop can be held to ([[lexical-grammar-as-data]]).

## Done when

The matcher's correctness is one theorem, and [[regex-dfa-compiler]]
cites the derivative automaton's language theorem for its soundness.

## What it assumes from elsewhere

- **[[kleene-algebra-with-tests]]** takes regular languages as a model.
  Assumed here: nothing.
