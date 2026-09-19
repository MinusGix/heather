---
title: A  declaration form for the fn … → Type families that specifications are made of
status: open
labels: [frontend,syntax,ergonomics,design,tooling]
created: 2026-09-18
updated: 2026-09-19
---

A specification written in Heather is mostly `fn … → Type`, and nothing in the
declaration says "this is a type family" rather than a program. In
`docs/showcase/calc_text.hthr` seven of the declarations are that shape —
`all_of`, `nonempty`, `RunSpec`, `OpSpan`, `OpRun`, `WellFormed`,
`GrammarSpec`, `Checked`, `ParsedText` — and they read like functions that
happen to return `Type`.

Proposed: a `type` declaration form with the same body grammar a `fn` has, so
the recursion and the `match` stay exactly as they are and only the heading
changes.

```heather
type WellFormed(d: Derivation) = match d {
    Number(ds, tr) => nonempty(ds) ∧ ds.all(is_digit) ∧ tr.all(is_space),
    …
}
```

What it buys, in order of weight: a syntax-highlighting and reading cue that a
declaration is a specification (`scripts/check-tree-sitter` and the editor
grammars can colour it); a place for the checker to say "a `type` body must
land in `Type`" instead of discovering it from the return annotation; and a
name for the thing [[record-type-partial-application]] is currently forcing
people to write by hand. It is deliberately *not* a new kind of definition —
same elaboration, same unfolding, same conversion behaviour as the `fn` it
replaces — so the risk is in the grammar and the diagnostics, not the kernel.

Open: whether `type` should also accept the indexed-record partial application
that issue asks for (`type Spec(level) = Grammar(level)`), which would make the
two land together.

Raised while reading `docs/showcase/calc_text.hthr` as a language-quality
target (2026-09-18, [[sequence-parser-source]]).

## Log

- 2026-09-19: 2026-09-19: The load-bearing use is not the one this issue leads with. A
  highlighting and reading cue is worth having, but what `docs/showcase/calc_text.hthr`
  actually needs is a **name for a type that repeats**: the `recur` parameter's type

      (next: Cursor<Char>(source))
          -> nat::Lt(list_len(rest(source, next)), list_len(rest(source, begin)))
          -> Checked(0, source, next)

  is spelled out in full **seven times** across `parentheses_body`, `atom_body`,
  `factor_body`, `expr_body` and the three `checked_*` fixpoints, differing only in
  the tier. The six `fn … -> Type` declarations the issue counts are a smaller
  matter than that one repetition, and it is the case where `type` has to accept
  partial application to help at all — which ties it to
  [[record-type-partial-application]]'s open question rather than leaving it
  optional.
