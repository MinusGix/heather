---
title: cong's cannot-generalize error names the same two terms as both the difference and the match
status: open
labels: [frontend,elaboration,diagnostics]
created: 2026-09-19
updated: 2026-09-19
---

`cong`'s "cannot generalize" error renders only the surface spelling of the
terms it compared. When the reason it declined is an **implicit argument** —
the raw-Σ-code vs `El(code)` spelling of the same type, which `lgg.rs` matches
by structural `==` with no conversion (a deliberate decision,
[[congruence-by-anti-unification]] §3 decision 2) — the message contradicts
itself on its face. Two verbatim examples, from converting
`docs/showcase/calc_text.hthr` to `calc` chains
([[showcases-predate-their-ergonomics]], 2026-09-19):

```
error: cannot generalize: the goal's two sides agree down through
`application`, and differ under it at `application` against `constructor value`
(`rest(source, got.end)` against `Nil`)., and the proof's endpoints are
`rest(source, got.end)` and `Nil` — every differing position has to be exactly
the proof's endpoints
```

The differing position it names and the endpoints it names are the *same two
strings*. A reader following the instruction ("every differing position has to
be exactly the proof's endpoints") concludes the condition is met and has
nowhere to go. The same shape appeared at `paren_grammar` with
`Cons(ofNat(41, decide_yes(refl)), append(close_trail, rest(source, end)))` on
both sides of the comparison.

A third variant in the same run is honest but uninformative — "the proof's
endpoints do not spell as surface" with `sum type` against `El`, and `True`
against `El` — which at least says *something* differs invisibly, but not
where or what to write instead.

What would fix it, cheapest first:

1. **When the two terms render identically, say so and render the difference.**
   The walk in `lgg.rs` already has both kernel terms at the position where
   `==` failed; a second pass that finds the first structurally differing
   subterm *including implicits* and prints that pair is the whole fix. The
   bounded `Debug` on kernel terms (`crates/kernel/src/fmt.rs`) is already safe
   to use for this.
2. **Name the likely cause.** A code/`El` mismatch at a type argument is the
   recorded common case; the message can say "the two sides spell the same type
   two ways (`El(code)` against the raw code), which this solver compares
   structurally" and point at the explicit-lemma fallback.

Not proposed here: making the comparison conversion-aware. That is decision 2
of [[congruence-by-anti-unification]] §3 and it was taken for good reasons
(linear, terminating, loud failure). This issue is about the *message* only.

Found while converting a real client rather than by reasoning about the
solver, which is the ranking datum: 4 of the 15 `cong` sites a single showcase
file offers hit this, and two of the four produced the self-contradicting form.
