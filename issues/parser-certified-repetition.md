---
title: many and some carry no span contract, only a consumption bound
status: open
labels: [stdlib,parser,proofs,design]
created: 2026-09-18
updated: 2026-09-18
---

`many` and `some` carry a `Consumes` certificate — enough to justify the
recursion — but no `Post`/`Sound` contract, so a caller that wants to know
*what* a repetition matched has nothing to compose. Every other combinator has
one (`bind_post`, `choice_post`, `rebase_post`, `map_post`, `recognize_post`).

The missing statement is a chain of adjacent spans:

```heather
fn Repeated<T, A>(relation, source: List<T>, begin, end: Cursor<T>(source), xs: List<A>) → Type {
    match xs {
        Nil => begin.offset = end.offset,
        Cons(x, ys) => Exists<Cursor<T>(source)>(λ middle =>
            And<relation(source, begin, middle, x), Repeated(relation, source, middle, end, ys)>),
    }
}
```
with `many_post : Sound(many(p, progress), Repeated(R))` given `Sound(p, R)`, and
`some_post` above it. The proof has to push the postcondition through the
`rebase`/`map_at` that `many_at` is written with, and induct on the same
`list_len(rest(source, begin))` measure the parser uses.

Found while writing the scannerless calculator ([[sequence-parser-source]]),
whose atom tier needs a certified digit run: a multi-digit numeral is the first
consumer in the tree that repeats *and* has to prove what it consumed. That
showcase hand-rolls a `checked_run` specialized to a character class
(`RunSpec(cls)` = the characters are in the class and are exactly the span),
which is this contract at one relation and about twenty lines. The hand-rolled
version is the datum for what the general one should say; it is not a
workaround to keep.

Note the hand-rolled run is *total* — an empty run is a run, so it returns a
certificate rather than a `Reply`. A general `many_post` has the same
character, and `some_post` is where failure re-enters.
