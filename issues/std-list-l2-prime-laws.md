---
title: std/list: the laws L2 did not state — foldl, filter, zip/len
status: closed
labels: [stdlib,proofs]
created: 2026-08-17
updated: 2026-08-17
---

Wave **L2′** of the library push. [[std-api-waves]] owns the sequencing that
put it here (waves 0–2, L1 and L2 are spent; the user called L2′ + L3 as one
round); this issue owns its content and the rankings it produces.

L2 stated seven laws plus three bonuses, and the shape of what it left out is
not random. Three of L1's functions came in with **no law at all**:

- **`foldl`** — the only recursion in the file whose accumulator changes, and
  therefore the only one whose laws all have to be stated at a *generalized*
  accumulator ([[ih-generalization]] at higher order, which the L1/L2 round
  ranked #2 without yet having to prove anything about it).
- **`filter`** — `len_filter` is a bound, not a law. What `filter` does to
  `append`, to itself, and to `map` is unstated.
- **`zip`** — nothing relates it to `len`, so `zip` is pinned only by the
  computation test.

## What it assumes from elsewhere

- **[[std-api-waves]]** owns sequencing. Assumed here: only that L2′ is
  writable now.
- **[[ih-generalization]]** owns the curried-recursion workaround. Assumed
  here: only that `foldl`'s accumulator is already returned as a function, so
  its laws are stated as `(z: B) -> …`.
- **[[decided-case-convoy]]** owns branch-on-a-decided-predicate. Assumed
  here: nothing — whatever `filter`'s `Bool` scrutinee costs is this round's
  output.

## What landed (2026-08-17)

Ten laws into `lib/std/data/list.hthr` (419 lines → 777 with L3's `Mem` kit), each
one the first fact its function has:

| function | laws |
|---|---|
| `foldl` | `foldl_append`, `foldl_rev` (`= foldr` with the function flipped), `foldl_len` |
| `filter` | `filter_append`, `filter_filter`, `filter_map` |
| `zip` | `len_zip` (`= min`), `zip_map_fst`, `zip_map_snd` (both `= take`), `zip_swap` |

Coverage: `crates/elab/tests/lib_std_list.rs` gains
`the_l2_prime_laws_are_present` (all ten, applied at open arguments — every
`foldl` law at an **open accumulator**, which is the axis a test at `0` would
miss) and five equations in `the_api_computes`.

Three findings the scope did not predict:

1. **`foldl`'s currying was not a tax here, it was the statement.** The L1/L2
   round ranked [[ih-generalization]] #2 off the *definition*'s shape, guessing
   the laws would pay for it. They do not: every `foldl` law is stated
   `(z: B) -> …` because that is what the law *is* — `foldl_append` at a fixed
   `z` is false — and the curried definition is then exactly the right shape.
   The workaround and the mathematics agree, which is a better outcome than the
   ranking assumed and worth recording against the next currying complaint.
2. **`foldl_rev` is the only law in the file that needs another law of its own
   function.** `rev` is defined by `append` and `foldl` says nothing about
   `append` by computation, so the two folds meet only through `foldl_append`.
3. **The `zip` laws cost nothing at all.** `min` descends on both arguments
   exactly as `zip` descends on both lists, and `take` is curried in its index
   for the same reason, so all three `zip`/`len` laws are `cong_*` over the tail
   with no arithmetic. The one arm that needed thought is `zip_map_snd`'s
   `Nil`: `take(ys, 0)` is stuck until its LIST is a constructor, so that arm
   splits `ys` and its mirror image does not.

## The ranking this round produced

Covers **both** halves of the round — L2′ here and L3 in
[[std-list-mem-and-perm]], which points at this list rather than repeating it.
Ordered by what it cost to write the file the way the API should read:

1. **[[goal-motive-by-scrutinee-abstraction]]** (filed). Seven of the round's
   declarations write an inner motive whose whole content is the body of the
   function the goal already mentions; in `filter_append` six of eight lines are
   that motive. The elaborator already abstracts a scrutinee that occurs in the
   goal *syntactically* (`take_append_drop`, `len_zip`) — it just does not whnf
   the goal first. Controls run: deleting the motive is refused.
2. **[[decidable-equation-carrier]]**, and this is the round's sharpest *design*
   datum even though it costs the fewest lines. It puts `Mem` and `count` — two
   specifications of the same algorithm — on opposite sides of a language
   boundary: membership needs only `=` and is polymorphic, counting must
   *decide* an equation, an instance cannot be keyed on one, so `count` is at
   `Nat` and the polymorphic list API has a permanent hole. Logged there.
3. **[[congruence-by-anti-unification]]**, third round running. Three sites:
   `filter_filter`'s `j` (a rewrite under a `match` context, motive written by
   hand) and the two `cong_fn(λ (n: Nat) => or_pick(eq_dec(a, h), n, Succ(n)),
   …)` in `count_insert`/`count_isort`. Every one of the three contexts is
   determined by the expected type. Also the round's only `sym`: the equation
   [[match-with-equation]] binds is `scrutinee = pattern`, and rewriting the
   *goal* wants the other direction.
4. **[[absurd-at-nat-numerals]]** (filed). `Mem`'s negative control could not be
   written at `Nat` — `absurd` reads a constructor equation only at a declared
   inductive — so it is written at `Bool` and the `Nat` cost (one `succ_inj` per
   unit of numeral distance) is recorded rather than absorbed into a helper.
5. **[[type-owned-namespaces]]**, first real customer of a prediction made
   2026-08-05: with `list` and `option` both imported a bare `map` resolves to
   **neither** — it reaches the prelude's vector `map` and reports that its
   receiver has to be a vector. `list::map` is the workaround in the test.
   Logged there.
6. **[[polymorphic-argument-with-unsolved-callee]]** (filed). `map(zip(xs, ys),
   swap)` is refused; either spelling the callee's type arguments or
   η-expanding the argument fixes it, so the cost is one line. Filed for its
   shape — the third consecutive round whose refusal is a polymorphic callee
   with an unsolved type argument.

Not ranked, because their owners are mid-fix and both were predicted: goal
displays print raw `El` ([[le-diagnostics-print-raw-el]]) and a refused arm
reports as a bare `the kernel rejected 'f': NotConvertible` naming no subterm
([[check-fallback-discards-expected-type]]). Cost here: every one of the
round's four refusals — three deliberate controls and one real mistake
(`zip_map_snd`'s `Nil` arm) — arrived with no usable location. It cost minutes
rather than hours only because each was predicted before it was run.

**Nothing was encoded around.** One law is deliberately *unstated*:
`mem_filter`'s converse needs `p(a)` as a hypothesis, whose only available
spelling is `p(a) = True`, which [[class-ops-prop-vs-bool]] bans from a
specification. The `Decide`-valued `filter` that [[std-list-api]] called "a
second function, not a replacement" is what would state it, and this is its
first customer; logged there rather than written.

## Log

- 2026-08-17: LANDED (2026-08-17): ten laws into lib/std/data/list.hthr, plus two new tests in crates/elab/tests/lib_std_list.rs. See §What landed and §The ranking this round produced above — the ranking covers BOTH halves of the round (L2' here, L3 in [[std-list-mem-and-perm]]) and is stated once. Residue has owners before closing (README rule 3): the seven restated motives are [[goal-motive-by-scrutinee-abstraction]] (filed, ranked #1), the rewrite contexts are [[congruence-by-anti-unification]], the unstated mem_filter converse is [[class-ops-prop-vs-bool]]'s second filter, the bare-map resolution is [[type-owned-namespaces]], and zip_swap's eta-expansion is [[polymorphic-argument-with-unsolved-callee]] (filed).
