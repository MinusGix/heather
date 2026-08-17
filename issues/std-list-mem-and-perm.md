---
title: "std/list: Mem by recursion, and insertion sort's permutation half"
status: closed
labels: [stdlib,proofs]
created: 2026-08-17
updated: 2026-08-17
---

Wave **L3** of the library push, taken with [[std-list-l2-prime-laws]] as one
round. [[std-api-waves]] owns the sequencing; this issue owns the content.

Two halves:

1. **`Mem` by recursion into Prop**, in `std/list`, with its kit — the
   `append`/`map`/`filter`/`rev` interactions. `Mem` needs only `=`, so it is
   polymorphic, unlike anything that has to *decide* membership.
2. **The permutation half of `insert`/`isort` correctness.** `Sorted` and the
   sortedness half landed 2026-08-17 in `lib/list_algos.hthr`; "sorts" is half
   a specification, and the missing half is that the output is a rearrangement
   of the input.

## The fork this round has to pick, and why it is not L4's

[[std-api-waves]] records that L4 — a general permutation *relation* — sits
behind [[indexed-families]], and that the permutation half forks: state it by
a `count` function needing decidable equality, or by a `Perm` relation. This
round picks and records; it does not open L4.

## What it assumes from elsewhere

- **[[std-api-waves]]** owns sequencing. Assumed here: only that L3 is
  **unblocked** — state the relation by recursion and reach its decider by
  resolution or by name, as `lib/list_algos.hthr` already does.
- **[[decidable-equation-carrier]]** owns the missing (class, carrier-syntax)
  key that would let `Decide` reach an equation. Assumed here: only that
  `nat::eq_dec` is called by name today.

## What landed (2026-08-17)

**`Mem` and its kit, in `lib/std/list.hthr`** — a recursion into `Type` beside
`nat::Le` and `list_algos`'s `Sorted`, plus `not_mem_nil`, `mem_head`,
`mem_cons`, `mem_append_l`, `mem_append_r`, `mem_append`, `mem_append_iff`,
`mem_map`, `mem_filter`, `mem_rev`. `std/list` gained `import logic;` to hold
it: the module had never needed `Or`/`False`/`Iff` before, which is one measure
of how much of a list API can exist with no relation in it.

**The permutation half, in `lib/list_algos.hthr`** (136 lines → 319) — `count`,
`pick_succ_comm`,
`count_insert`, `count_isort`, `len_insert`, `len_isort`, `mem_insert`,
`mem_isort`, and `isort_correct`, which is the library's first specification
stated as a conjunction of a relation and an extensional equality:

```heather
theorem isort_correct(xs: List<Nat>):
    And<Sorted(isort(xs)), (a: Nat) -> count(a, isort(xs)) = count(a, xs)>
```

Coverage: `crates/elab/tests/lib_list_algos.rs` gains
`the_permutation_half_is_present` (cited through `isort_correct`'s *second*
field, so deleting `count_isort` and leaving sortedness alone fails) and
`sorting_and_counting_compute`, whose negative control is
`count(2, [2,1,2]) = 3` — a permutation theorem proved only at open lists would
go on passing over a `count` that always answered `0`.

### The fork, as taken: `count`, not `Perm`

Recorded per [[std-api-waves]]'s instruction. **`count` won, and not by
default.** A `Perm` relation is inductive over two lists at once, i.e. an
indexed family ([[indexed-families]]), which is wave L4's; `count` needs only a
decidable equation and is writable today. But the reason to prefer it is not
availability: `count_isort` is the *extensional* statement of multiset equality,
it is what a caller checking a sorter actually wants, and it **computes** — at
closed lists both sides reduce to numerals and the theorem is `refl`, which no
relation does. What L4 would buy that this cannot is a permutation fact that
can be **transported**: composed, inverted, used to carry an arbitrary predicate
from one list to the other. An equality of counts at each `a` is a fact about
counts. That is the argument for L4 that this round can now state precisely,
and it is stronger than "the relation is the textbook definition".

`mem_isort` is kept alongside as the strictly weaker statement, because it is
what `Mem` is for and it is three lines on top of `mem_insert`.

### Three things the halves taught that the scope did not predict

1. **The line between the two halves is decidable equality, and it runs through
   the same algorithm.** `Mem` is polymorphic and lives in `std/list`; `count`
   is at `Nat` and lives with the algorithms. Nothing about counting is
   `Nat`-specific — it needs to decide `a = h`, an equation has no head to key
   an instance on ([[decidable-equation-carrier]]), so `decide<a = h>()` — the
   spelling `insert` uses for `Le` two declarations above — has no instance to
   find and `eq_dec` is named. The dictionary-passing `count` (take the decider
   as a parameter, thread it through every call site) was **not written**: it
   works, and an encoding that works is an erased ranking datum.
2. **The permutation proof's real content is one lemma about neither lists nor
   sorting.** `pick_succ_comm` — two independent decisions each of which may add
   one commute — is the whole difficulty of `count_insert`; the rest is the IH
   rewritten in underneath it. Four cases, all `refl`, and only the `Inl` side
   needs its inner split, because substituting `Inr` makes both sides the same
   term.
3. **Sortedness cost more than permutation.** The half that landed 2026-08-17
   needed `le_of_not_le` and a new `std/nat` line; this half needed nothing from
   `std/nat` but `eq_dec`, and every `decide<Le(x, h)>()` motive was already
   written in the file next door. The scope expected the reverse.

## The ranking this round produced

The round was L2′ + L3 together and its ordered ranking is stated **once**, in
[[std-list-l2-prime-laws]] §The ranking this round produced. The two items this
half contributed are #2 ([[decidable-equation-carrier]], the round's sharpest
design datum) and part of #1 and #3 (three of the seven restated motives, and
the two `cong_fn` contexts).

## Log

- 2026-08-17: LANDED (2026-08-17): Mem and its ten-lemma kit in lib/std/list.hthr, count/count_isort/isort_correct in lib/list_algos.hthr, two new tests in crates/elab/tests/lib_list_algos.rs including the count negative control. See §What landed above, which records the fork as taken (count, not Perm) and the argument it leaves L4. Residue has owners: the polymorphic count is [[decidable-equation-carrier]] (ranked #2), the Nat negative control is [[absurd-at-nat-numerals]] (filed), the transportable permutation relation is wave L4 behind [[indexed-families]] and its row on [[std-api-waves]].
