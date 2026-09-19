---
title: cong's cannot-generalize error names the same two terms as both the difference and the match
status: closed
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

## Log

- 2026-09-19: **Landed.** The message no longer names the same two terms as both the
  difference and the match, and two neighbouring warts the round exposed went
  with it. Nothing about the *rule* changed — decision 2 stands, the witness test
  is still structural `==` with no conversion — this is the message only, as the
  body proposed.

  `crates/elab/src/lgg.rs` grows `first_difference(x, y)`: the same walk
  `lgg_body` already does, with the witness test switched off, so every
  difference stops it. What comes back is a `Mismatch` — a *position*, in the
  one-word former vocabulary the rest of the message uses — and a `{:#}`
  alternate `Display` renders it as a phrase for a caller that is already
  mid-sentence. No kernel term is printed, which is the bound
  [[lgg-diagnostic-dumps-kernel-terms]] set and this round keeps.

  Three clauses in `Elaborator::cong_mismatch`:

  1. **The endpoints case** (the one this issue was filed for). When the side
     the walk stopped at spells exactly like the proof's endpoint but is not
     that term, say so and say where they part. Measured on the site that
     produced the issue, `calc_text`'s `finish_text`:

     > … — every differing position has to be exactly the proof's endpoints (…
     > §3). That position is the one the proof witnesses, and it looks like it:
     > the right side there and the proof's right endpoint both spell `Nil`, but
     > they are not the same term — they part under `constructor value ▸ inl` at
     > `pair` against `variable`. The witness test is structural, never up to
     > conversion (… §3 decision 2), so a difference the surface spelling drops
     > still declines. Spell the endpoint the way the goal does, or use an
     > explicit congruence lemma.

  2. **The goal case**, found while building a minimal reproduction and the more
     common presentation of the two: the *goal* prints as ``wrap(c, Red) =
     wrap(c, Red)`` above a sentence saying those two sides differ. Same
     treatment, same walk.

  3. **`El` against a type code** gets named outright — one type spelled two
     ways, convertible but not equal as terms — since that is the shape behind
     most of these and a reader should not have to know how a type is
     represented to act on the message.

  Two fixes the round found on the way, both in the same message:

  - **An internal binder name was reaching the reader.** The position clause
    rendered `` (`#scrut` against `(trivial, trivial)`) `` — a name that cannot
    be looked up, beside a raw Σ payload. That is the same wall as
    [[lgg-diagnostic-dumps-kernel-terms]], merely small enough to print. A side
    whose spelling carries `#` is now not spelled; the formers still locate it.
  - **A stray period.** When the goal did not spell, the `else` branch pushed a
    bare `.` and the next clause opened with `, and the proof's endpoints`,
    giving ``against `Nil`., and the proof's …``. A clause that cannot be said
    now leaves no mark either.

  Tests: five unit tests on `first_difference` in `lgg.rs` — including the case
  it exists for, two terms differing only inside a type annotation the speller
  drops (`True` against `El`) — and three integration tests in
  `crates/elab/tests/congruence_lgg.rs`: the goal case, the no-internal-names
  claim, and a **negative control** asserting an ordinary mismatch gains no extra
  clause, so none of this becomes noise on every refusal. The existing
  diagnostic tests' `< 600` character bounds are untouched and still hold: the
  new clauses fire only where the old message was unreadable.

  One coverage gap, stated rather than papered over: clause 1's live witness is
  `docs/showcase/calc_text.hthr`, which the snippet harness cannot load. Four
  attempts at a prelude-only reproduction all landed on clause 2 instead — a
  computed scrutinee refines the goal, and the written endpoint goes with it — so
  clause 1 is pinned at the `first_difference` level and verified by hand on the
  showcase. A test for it wants the library-loading harness and a smaller
  `finish_text`-shaped fixture than this round could find.
