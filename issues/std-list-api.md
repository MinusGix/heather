---
title: "std/list: the L1 API and the L2 law kit"
status: closed
labels: [stdlib,proofs,frontend,ergonomics]
created: 2026-08-17
updated: 2026-08-17
---

Waves L1 and L2 of the library push, taken as one round. [[std-api-waves]]
owns the sequencing that put them next (`0 → 1 → 2 → L1 → L2`); this issue
owns their content, and the rankings they produce.

`std/list` is 76 lines to `std/nat`'s 1029: `append` with two laws, `map` with
**none**, `List::nth`. `len` and `rev` are stranded in `lib/list_algos.hthr`
next to a private `plusl`. That asymmetry is the round.

## L1 — the API

Into `lib/std/list.hthr`:

- **Move** `len` and `rev` (+ `rev_append`, `rev_involutive`, `cong_append_l`)
  out of `lib/list_algos.hthr`, which keeps them by `import list;` exactly as
  it already keeps `cong_cons` and the append laws (the 2026-08-07 precedent).
- **Retire `plusl`.** It exists because `nat::add` recurses on its *second*
  argument while `nth_append_r`'s index has to reduce as `xs` is peeled off
  the front. That is an argument-order accident, not a missing feature.
- **New:** `foldr`, `foldl`, `filter`, `take`, `drop`, `replicate`, `zip`,
  `head`, `tail`, `last`.

Three shape decisions this round has to make, recorded here when it makes
them: what `filter`'s predicate is (`A -> Bool` is a *program*, so the
[[class-ops-prop-vs-bool]] doctrine does not forbid it — that doctrine is
about specifications); what `head`/`last` return on `Nil`; and what `zip`
pairs with, since the library has no product type.

## L2 — the laws

`map_id`, `map_map`, `map_append`, `len_map`, `len_append`, `rev_len`,
`foldr_append`. These are the seven [[std-api-waves]] named; anything else the
round proves is a bonus and gets recorded, not assumed.

## What it assumes from elsewhere

- **[[std-api-waves]]** owns sequencing. Assumed here: only that L1/L2 are
  next and unblocked.
- **[[ih-generalization]]** owns the curried-recursion workaround. Assumed
  here: only that a two-argument recursion whose second argument varies is
  spelled curried (`nth`, `sub`, `min`/`max` are the precedents), so `take`
  and `drop` will be too.
- **[[guarded-to-option-adapter]]** owns partial functions getting an
  `Option` face by adapter. Assumed here: nothing — `head`/`last` are written
  in whatever spelling is available today, and if that ranks the issue, the
  ranking is this round's output.

## Why this round, per [[list-algorithms-exercise]]'s method

`Nat`'s waves exercised recursion on one first-order argument. `List`'s
exercise polymorphism and **higher-order arguments** (`foldr`, `filter`,
`map`'s laws) for the first time at library scale. The two rounds before this
one both predicted their risk correctly as *notation and grammar* rather than
restatement; whether that holds where the arguments are functions is the
question this round answers.

## What landed (2026-08-17)

`lib/std/list.hthr`, 76 lines → 419. `lib/std/pair.hthr` is new (14).
`lib/list_algos.hthr` went 218 → 136 and is now only algorithms. Coverage:
`crates/elab/tests/lib_std_list.rs`, three tests — the closure checks, the law
kit applies at open arguments, and the API *computes* at closed ones.

The three shape decisions the scope asked for, as made:

1. **`filter` takes `A -> Bool`.** [[class-ops-prop-vs-bool]] bans `Bool` from
   specifications, and `filter` is a program; the `Decide`-valued predicate is
   a different function, not a correction of this one, and nothing wants it
   yet.
2. **`head`/`last` return `Option<A>`**, `tail` is total. Written, not stalled:
   `Option<A>` is the honest type for the head of a possibly-empty list, so
   this is not an encoding around a missing feature. [[guarded-to-option-adapter]]
   now has its first two customers and knows what it would be rewriting.
3. **`zip` pairs with a new `std/pair`**, a module rather than a declaration
   inside `list`: a product is not a list notion, and `logic::And` is the same
   shape with the wrong field names for data.

Retiring `plusl` cost nothing and taught the round's cheapest lesson: it
existed only because `nth_append_r`'s index was written `plusl(len(xs), i)`,
and `add(i, len(xs))` steps exactly when `append` does. A whole private
function was paying for an argument order.

## The ranking this round produced

1. **[[curried-tail-type-arg-inference]]** (filed). The only thing the round
   could not write as intended. `zip<A, B>` must spell its type arguments
   forever, because currying ([[ih-generalization]]) puts `B` where inference
   ([[exists-type-arg-not-inferred]]'s rule) does not look. Two individually
   correct features; the collision is new because `zip` is the library's first
   *polymorphic* two-structure recursion.
2. **[[ih-generalization]]**, at higher order for the first time: `foldl`'s
   accumulator, not an index, is what has to be curried. Logged there.
3. **[[match-arg-of-polymorphic-callee-needs-motive]]** (filed). `len_filter`'s
   inner `match` had to be given a motive stating the type its callee already
   knows, because a polymorphic callee with an unsolved type argument leaves
   its argument in inference position. Costs two lines here; the trigger is
   ordinary in any polymorphic program.
4. **[[le-diagnostics-print-raw-el]]**, second customer: an unfilled goal in a
   `len_append`-shaped proof prints its statement as several hundred columns of
   kernel encoding. Logged there.

Nothing here blocked the wave, which is the difference from wave 3 — that one
stalled on a feature that had to land first ([[recursion-at-deeper-subterms]]),
and this one produced four rankings it could route around. Two of the four are
the *same shape*, and that is the finding worth carrying forward: a polymorphic
callee whose type argument is unsolved (`zip`'s curried `B`, `len`'s `A` under
a `match`) is where the language stops helping. Neither was predictable from
the `Nat` waves, which had no type arguments to leave unsolved.

## Log

- 2026-08-17: Landed; see §What landed and §The ranking this round produced above. Residue has owners before closing (README rule 3): the unstated laws are [[std-api-waves]]'s new L2' row, zip's inference is [[curried-tail-type-arg-inference]], head/last's spelling is [[guarded-to-option-adapter]], the goal display is [[le-diagnostics-print-raw-el]].
- 2026-08-17: Both language gaps this round ranked are FIXED, same day (2026-08-17): [[curried-tail-type-arg-inference]] (spilled arguments now solve the callee's type parameters) and [[match-arg-of-polymorphic-callee-needs-motive]] (a motive-less match in inference position takes a constant motive from a non-binding arm). lib/std/list.hthr lost both workarounds — zip(xs, ys) is unspelled and len_filter's inner motive is gone — so the file now reads the way the round wanted to write it. The second fix reached further than its issue predicted: an unannotated `let x = match r { … };` elaborates, and three suite probes that had been using the refusal as a stand-in for 'an expression whose type is unknown' had to be rewritten onto every-arm-binds matches. One new issue came out of the controls: [[check-fallback-discards-expected-type]].
