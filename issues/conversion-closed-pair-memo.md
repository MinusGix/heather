---
title: Conversion evaluated every node of two spellings of one type, and judged the same closed pair again in every query
status: closed
labels: [kernel,conversion,performance]
area: kernel
created: 2026-11-10
updated: 2026-11-10
---

The kernel gate's largest cost on the showcase was conversion of two
spellings of one large type. Found by the miss sampler
([[perf-profile-build-target]]) on `docs/showcase/calc_parser.hthr`: of the
time inside `Tc::conv_ty` misses, half was `Sigma` against `Sigma`, a
thousand queries of milliseconds each, nearly all in
`lib/std/tactic/grind.hthr`. One excerpt printed two types of several
hundred thousand characters each that differ where one side names a code
(`El(u^·)`) and the other writes it out.

## Why it cost that

Two things, and they multiply.

**Every node of both sides went through the value machine.** To find that
`Σ(x : A). B` and `El(Σ̂(x : a). b)` are both a `Σ`, conversion evaluated
each side to weak head normal form: a closure and a value allocated per
node, a fresh `El` node per decoded child (`Eval::decode`), a footprint
lookup on each fresh node, and a verdict-memo probe keyed by addresses that
did not exist a moment ago. The two sides were already written as the same
former; nothing had to be computed to see it.

**The same pair was judged again and again.** An elaborated type is a dag:
a named code is mentioned from many places, and so is its spelling. In
`grind::by_diseq` the checker entered `Conv::ty` 827,000 times on closed
sub-structures, over 16,000 distinct pairs of nodes, once a decoded code is
identified by the code under its `El` and not by the `El` node the decoding
allocated. The per-query verdict memo could not see this (its keys are the
arena's closures, fresh each time), and the gate's own memo
([[kernel-gate-conversion-reuse]]) works at the root of a query.

## What was built

In `crates/kernel/src/conv.rs`, for the value domain only (`Dom::SPELLED`;
the rewriter oracle takes neither, so `tests/conv_differential.rs` holds
both to the specification):

- **A lockstep walk** (`Conv::lockstep`, `Spelled`, `Former`). A type is
  read as it is spelled: itself, or the decoding `El^l c` of a code. Two
  spellings that show the same former (`Nat`, `Ty`, `Unit`, `Empty`,
  `sEmpty`, squash, `Π`, `Σ`, `W`, `+`, `Id`, `sEq`) are compared component
  by component on the syntax, and only a pair that is not one former goes
  to the domain. The binders passed are pushed onto the scope only when
  such a pair is reached (`Under`). Codes compared as terms at a universe
  are walked the same way with their leaves compared as codes, because `El`
  is not injective.
- **A table of convertible closed pairs** (`ClosedPairs`, in the
  `GlobalCache` beside Ψ, so for one gate and all its queries). A closed
  spelling reads no local variable, so under one Ψ it is one type whatever
  Γ or environment it is met in. The key is the two nodes (owned, so an
  address stays its node's), the level, the layer and which judgment it was
  (types, or codes). Asked at `Conv::ty`, at `Conv::tm_at_univ`, and where
  the walk hands a pair to the domain. Bounded, never evicting, and only
  for judgments that cost a few units of fuel: a pair of leaves is judged
  again for less than an entry costs.

## What has to hold

- The formers the walk reads are weak head normal, a code's `El` decodes to
  the former in one step with the `El`s of its components
  (`reduce.rs::step_type_frame`), and `Conv::ty_nf` compares exactly those
  components in the scopes the walk uses. So the verdict is the one
  reducing both sides reaches; what is skipped is the domain's copy.
- Only `convertible` is kept, never exhaustion, and not while a premise is
  queued or a provisional verdict could have been stood on
  (`Conv::closed_learn`).
- A walk started from open types (`Conv::ty_root`) keeps nothing it has not
  asked the footprint of. The first version got this wrong: under no binder
  it took a pair for closed because the walk's root was, which a root query
  does not promise.
- Two types kept convertible are not two convertible codes (`Vec(T; 0)` and
  `Unit`).
- A table serves the Ψ it was built for, interface boundary included
  (`GlobalCtx::withheld` is not part of a binding's identity).
- A debug build judges a sampled hit again without the table
  (`checks::verify_this_skip`).
- One judgment costs the same budget at either of the checker's entries.
  `tests/typing_differential.rs`'s fuel sweep found that it did not: the
  checker's older memo judges a kept pair again through `Conv::ity_root`,
  which had no walk, so at a budget of a few units it ran out where
  `ty_root` had answered. `ity_root` now walks two spellings as `ty_root`
  does. The table never evicts for the same reason: within a gate a
  judgment must not cost more later than it did earlier.

`crates/kernel/src/conv/spelled_tests.rs` has a test for each, and the
guards for the third and fourth were each removed once to watch their test
fail.

## Left open

- **Across declarations**: [[conversion-closed-pairs-across-gates]]. The
  table is one gate's, and every declaration of `grind.hthr` meets the same
  giant type and walks it once.
- **Open pairs**: [[conversion-walk-over-two-environments]]. About an
  eighth of the entries in `by_diseq` are closures whose bodies read their
  environment.
- **Hashing**: [[conversion-memo-hash-cost]]. The per-query verdict memo's
  SipHash, and `PtrHasher`'s empty low bits.

## Log

- 2026-11-10: Built on `wip/conv` (2026-11-10). Numbers, all on the cloud box, width one,
  `docs/showcase/calc_parser.hthr` cold unless said.

  **Before**, from the miss sampler (`HEATHER_VALUE_METRICS=1`, metrics build):
  39,367 misses, 4.83 s inside them. `Sigma`/`Sigma` 2.50 s over 1,243 misses
  (2.0 ms each), `Sum`/`El⌜⌝` 0.72 s over 11,682, `El(?)`/`El(?)` 0.30 s,
  `El(?)`/`Sigma` 0.22 s, `Id`/`Id` 0.22 s, `W`/`W` 0.17 s. In
  `lib/std/tactic/grind.hthr` alone, `Sigma`/`Sigma` was 1.98 s over 741.

  **One item**, `grind::by_diseq` (`--only`, same build, the two halves
  switched by hand): 1,783 misses of 109,241 queries in each.

  | | gate | evaluator steps |
  |---|---|---|
  | neither | 326 ms | 327,796 |
  | walk only | 192 ms | 85,534 |
  | table only | 84 to 99 ms | 45,128 |
  | both | 55 ms | 11,343 |

  Under callgrind the item's conversion was 600 M instructions with the walk
  alone, 87% of its gate. `Conv::ty` was entered 826,962 times on pairs of
  syntactic closures: 502,930 closed with one former on both sides, over
  6,345 distinct pairs of nodes; 16,097 distinct pairs in all. The walk gave
  133,293 pairs back to the domain, 4,025 distinct.

  **The miss table after**, same sampler: 1.56 s inside misses (walk only
  2.20 s, table only 2.88 s). `Sigma`/`Sigma` 0.62 s (0.5 ms each),
  `Sum`/`El⌜⌝` 0.05 s, `W`/`W` 0.02 s. In `grind.hthr`, `Sigma`/`Sigma`
  0.51 s over the same 741: what is left is each declaration's first walk of
  the type.

  **`scripts/perf ab --mode cold`** against master 6ab7e58, three interleaved
  samples:

  | | master | this |
  |---|---|---|
  | kernel gate | 7.00 / 6.82 / 7.12 s | 3.91 / 4.00 / 3.61 s (−44%, separate) |
  | wall | 18.70 / 18.70 / 19.00 s | 15.69 / 16.21 / 14.67 s (−16%, separate) |
  | `eval_steps` | 7,093,639 | 3,992,405 (−43.7%) |
  | `eval_drives` | 10,769,531 | 4,551,913 (−57.7%) |
  | `eval_delta_steps` | 839,179 | 599,156 (−28.6%) |

  `conv_misses`, `check_terms` and 34 other columns identical. Per item:
  `grind::by_diseq` 0.367 → 0.065 s, `with_reduct` 0.234 → 0.068,
  `read_fact_as` 0.167 → 0.036, `build` 0.189 → 0.060, `read_one`
  0.175 → 0.050.

  **`scripts/bench --check`** fails on this box on master as well (29 rows
  against the recorded baseline, 23 with this change), so it was read as a
  same-box comparison: `conv/vec-literal` 0.3× of master's time, everything
  else inside the run-to-run spread, including the `wf/` families run twice
  on each tree in alternation.

  Verified: `scripts/test -p heather-kernel-lib --lib` (155), `-p
  heather-kernel` (423, the differential suites among them).
- 2026-11-10: Rebased onto master at ab57366 (2026-11-10, after #544, #543 and #545; the
  kernel was untouched on master in between). `scripts/test --pr`, native
  certificate gates included: `== suite: 3634 passed, 0 failed, 2 ignored ==`,
  the same line as on the base before it.
