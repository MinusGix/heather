---
title: The regex language's compiler: a DFA, its soundness once, and Compile(name)
status: open
labels: [native,compiler,dsl]
created: 2026-11-01
updated: 2026-11-10
area: heather-in-heather
milestone: [nh-front]
---

The `regex` language (`lib/std/text/regex/regex.hthr`, docs/metaprogramming/value-definitions-design.md §4) has its term type, its meaning (`Regex::accepts`, Brzozowski derivatives), a parser and its `regex def` frontend; it has no compiler. This issue is the compiler half of `docs/compilation-vision.md` §3.3.

## Scope

- `Regex::dfa(r)`: a deterministic automaton for `r` (derivatives up to a similarity that makes the state set finite, or a position automaton), and `Dfa::run`.
- `theorem Regex::dfa_sound(r, s): r.dfa().run(s) = r.matches(s)`, proved once for every term.
- A table-driven runner as an `rt` function with its own `Compile` instance, and `regex def` publishing `instance Compile(name)` from the soundness theorem, once the `Compile` class exists ([[compile-typeclass-design]]).

## What it assumes from elsewhere

- [[runtime-fn-default-setup]] owns `Compile` instances for `runtime fn`s; assumed here only that a hand or generated instance has the same statement.
- [[generate-group-internal-references]]: with it, `is_hex` can be defined as `is_hex::term.accepts` instead of inlining the term twice.

## Done when

`regex def is_hex = "[0-9a-f]+";` publishes a `Compile(is_hex)` instance whose code is the DFA runner over `is_hex::term().dfa()`, cited by a `runtime fn` that calls `is_hex`.

## Log

- 2026-11-05: gardener: cites a file it shares with [[facts-on-demand]] (`docs/compilation-vision.md`).
- 2026-11-10: The language theory (denotation, derivatives, the derivative automaton and its language theorem) is now owned by [[regular-languages-by-derivatives]] under `math-formal-languages`; this issue keeps the compiler and `Compile(name)`.
