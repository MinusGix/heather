---
title: Show the rough parameter type in deferred-argument diagnostics
status: closed
labels: [frontend,elaboration,diagnostics,ergonomics]
created: 2026-09-21
updated: 2026-09-28
---

Found while changing parser `lookahead_at` from a `match` to a receiver call.
The module defines its own parser combinator named `map`, imports `result`, and
then writes:

```heather
fn lookahead_at<T, A>(source: List<T>, begin: Cursor<T>(source),
    r: Reply<T, A>(source, begin)) → Reply<T, A>(source, begin) {
    r.map(λ s => pure_at(source, begin, s.value))
}
```

Here `Reply<T, A>(source, begin)` reduces to
`Result<Success<T, A>(source, begin), Failure<T>(source)>`, and `pure_at`
returns another `Reply`. The intended `Result::map` reading would therefore
nest the result; `and_then` is the operation the code wants. Instead the site
reports only:

```text
this argument of `map` was deferred — the type of its parameter `f`
still mentions an implicit that could not be inferred; give the type
arguments (`map<…>(…)`) or write the call fully explicitly (`@map(…)`)
```

That message withholds both pieces of type information that make the mistake
quick to recognize: which visible `map` was selected, and the rough type of
the parameter that still contains the implicit. The suggested escape hatches
are consequently less useful than the information the elaborator already has.

The name interaction is reproducible independently of the parser body:
making `parser_combinators::map` visible reproduces the deferred-argument
message; removing that visible `map` gives the useful refusal at the callback:

```text
this has type `Result<Success<…>, Failure<…>>`, but `Success<…>` is expected here
```

Qualifying `result::map` gives the latter result too. Thus this issue is not a
request to make the ill-typed call elaborate. It owns the diagnostic produced
when name selection plus deferred application inference hides the type shape
that explains the refusal.

## Acceptance

- The parser repro still fails, but the diagnostic exposes enough of the
  selected callee and its rough receiver/`f` parameter types to distinguish
  the parser `map` from `result::map`.
- The displayed type shape makes the nested `Result` consequence visible once
  the intended `result::map` reading is selected, either in the primary error
  or a concise note.
- The message does not dump raw metas or kernel-only syntax; unsolved portions
  may use stable placeholders and ellipses.
- A genuinely underdetermined deferred argument retains the existing advice
  to supply type arguments or write the call explicitly.
- A qualified `result::map` version continues to report the direct callback
  mismatch, and the corrected `and_then` version checks.

## What it assumes from elsewhere

- **[[polymorphic-argument-with-unsolved-callee]]** owns whether genuinely
  deferred polymorphic arguments can be inferred. Assumed here: only that the
  deferred path remains possible and therefore needs an actionable diagnostic.

## Log

- 2026-09-28: Deferred-argument errors now include the selected callee's qualified name and
  rough explicit parameter types, with inferred pieces substituted and remaining
  implicits named as stable placeholders (for example, `f: Nat -> ?B`). The bounded
  surface speller elides unsupported shapes and exhausted budgets rather than
  printing raw kernel syntax. Existing type-argument and explicit-call advice is
  retained, including for bare operator arguments.

  The original `r.map(...)` repro now reaches the type-owned `Result::map` even
  with a visible parser `map`, and already reports the callback's nested
  `Result<Success<…>, Failure<…>>` versus the expected `Success<…>`. Regression
  coverage preserves that refusal, the fully qualified `result::Result::map`
  refusal, and successful `and_then`; explicitly selecting the visible parser
  `map(r, ...)` covers the deferred diagnostic and its `Parser` receiver type.
  An underdetermined polymorphic call checks partial substitution and retained
  advice, and a display unit test covers kernel-only shapes and depth elision.
- 2026-09-28: Validation: full `scripts/test` passed (3027 passed, 0 failed, 5 ignored);
  `scripts/issue check` passed with one pre-existing unrelated warning.
