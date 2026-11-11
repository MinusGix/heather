---
title: "Regular languages: denotation, Brzozowski derivatives, and a DFA of derivatives proved once"
status: open
labels: [stdlib,mathematics,automata,lexer]
area: mathematics
milestone: [math-formal-languages,self-lexer]
created: 2026-11-10
updated: 2026-11-11
---

Area 5 of the 2026-11-10 ranking. The mathematics under
[[regex-dfa-compiler]], which stays the compiler client.

`lib/std/text/regex/regex.hthr` parses regex syntax. `lib/lang/lexer` holds one
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

## Log

- 2026-11-11: First round, the denotation and the matcher.
  `lib/std/text/regex/regex_language.hthr`, over `regex.hthr`'s `Regex` (codes
  as `Nat`): `Regex::Denotes(r, w)` by recursion on `r`, with the star as
  a word cut into pieces (`Regex::Starred`, `Regex::Each`);
  `nullable_sound` and `nullable_complete`; `deriv_sound` and
  `deriv_complete` (the derivative by `c` denotes the words `w` with
  `c :: w` in the language; the star's case is `star_step`);
  `matches_iff`, which is the first half of "done when": the matcher's
  correctness is one theorem. Membership decides by running the matcher
  (`denotes_dec`, a `Decide` instance, `matches_refutes`), a `regex def`'s
  Boolean is membership (`accepts_iff`), and `deriv_word_denotes` restates
  the derivative at a word. `list.hthr` gains `append_nil_parts`; the pieces are joined by
  `algebra.hthr`'s `concat`. Probes in
  `lib/_tests/std/text/regex/regex_language_tests.hthr`.

  Kept `Regex` at `Nat` codes instead of a `Regex<A>`: the generator, the
  parser and `regex def` are written against it, and ranges need an
  ordered alphabet. A generic alphabet is a separate step if a second
  client wants one.

  Remaining: the language operations' laws up to extensional equality as
  a module of their own (for [[kleene-algebra-with-tests]]); derivatives
  modulo similarity are finitely many; a DFA record over a finite state
  type and the derivative automaton's language theorem (what
  [[regex-dfa-compiler]] cites); product and complement; longest-match
  tokenisation as a specification.

- 2026-11-11: Second round, automata and the automaton of derivatives.
  `lib/std/text/regex/regex_dfa.hthr`: `Dfa<S>` (start, step, accepting test,
  over any state type), `run_from` and `run`; `Dfa::residual` is the one
  theorem about what an automaton accepts (label every state with a
  language the accepting test and the step respect, and a run from a
  state accepts its label); `complement`, `both` and `either` with their
  run equations, so product and complement are done at the level of
  automata. `Regex::Same` (one language) with its congruences over `Seq`,
  `Alt` and `Star`. `Regex::automaton_by(r, step)` has expressions as
  states and any step that lands on the derivative's language;
  `automaton_by_accepts` says it accepts `r`'s language and
  `automaton_by_matches` that its run is the matcher's Boolean. Two steps
  are supplied: the plain derivative (`automaton`) and `deriv_simp`
  (`automaton_simp`), the derivative built with `Regex::alt` and
  `Regex::seq`, which apply the units and zeros; `Regex::simp` rebuilds an
  expression with them (`simp_same`). Probes in
  `lib/_tests/std/text/regex/regex_dfa_tests.hthr` (`(a|b)*` stays on one state
  under `deriv_simp`).

  The smart constructors take their Boolean tests as parameters
  (`alt_at`, `seq_at`): a `match h: test` in a proof does not reach a
  test under a folded definition, and a theorem over the tests as
  variables needs no motive.

  Remaining: the state type is `Regex`, which is not finite. Next is
  similarity (`Alt` associative, commutative and idempotent, which needs
  a Boolean equality on `Regex` with its soundness) and that the
  derivatives of an expression up to it are finitely many; or, by the
  checked-witness route, a builder that explores the reachable states
  with fuel and returns a table over `Fin(n)` together with the map from
  states to expressions that `Dfa::residual` checks, which is what
  [[regex-dfa-compiler]] needs and does not wait on the finiteness
  theorem. Both need the step over character classes instead of single
  codes. Then the language laws module for
  [[kleene-algebra-with-tests]] and longest-match tokenisation.
- 2026-11-11: Proof forms revised the same day, after Minus asked what kept them verbose: `≈` is designated at `Regex` with an `Equivalence` instance, so chains are `calc`; the `Same` lemmas take their expressions implicitly; existentials are taken apart by pattern; the catch-all cases are wildcard arms. What stayed manual is filed as [[case-split-on-a-definitions-tests]] (why `alt_at`/`seq_at` exist) and [[rel-cong-under-constructors]]. The modules moved to `lib/std/text/regex/`.
