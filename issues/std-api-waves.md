---
title: "Meta: the std API waves for Nat, List and Int"
status: open
labels: [stdlib,meta,design]
created: 2026-08-16
updated: 2026-08-17
---

Organizing issue for a deliberate **library** push rather than a feature push
(user, 2026-08-16): developing the core API for `Nat`/`List`/`Int` is how we
find out where the language is actually useful, what the API should look like,
and how checking behaves on workloads closer to practical ones. Per tracker
rule 2 this issue owns **sequencing only**; each wave's content and decisions
live in the issue named beside it.

## Where the library is (2026-08-16)

`std/nat`: `add` + `mul` with monoid kits, `leb`/`Le`, `sub` with one lemma,
five order lemmas. `std/bool`: both monoids. `std/list`: `append` with two
laws, `map` with **none**, `List::nth`. `std/option`: three functions.
`std/algebra`: Semigroup→Monoid→CommMonoid, `Default`, `Cmp`, `mconcat`.
`lib/list_algos.hthr` strands `len` and `rev` outside `std`.

## The waves

| # | contents | owner |
|---|---|---|
| 0 | ✅ **landed 2026-08-16** — `Empty`/`Not`/`And`/`Or`/`Iff`/`Exists` + `¬ ∧ ∨ ↔ ∃ ∀` | [[std-logic-module]] (closed) |
| 1 | ✅ **mostly landed 2026-08-16** — `Le` by recursion, `Lt`, the order + strict kit, `le_dec`, `le_iff_exists_add`; `sub` kit and `min`/`max` deferred | [[nat-order-kit]] |
| 2 | ✅ **mostly landed 2026-08-17** — `succ_inj`, `succ_ne_zero`, `zero_ne_succ`, `eq_dec`, `le_of_not_le`, and `Decide` over the connectives; `Decide` **at** `Nat` equality and order is blocked, see below | [[decide-class]] |
| 3 | `add_le_mono`, `mul_le_mono`, cancellation; `pow`, `half`/`even`/`odd`, `fact` | [[nat-order-kit]] (arith half unowned — file when scheduled) |
| 4 | `Nat::iter`/fold with `add`/`mul`/`pow` as instances | [[datatype-container-algebras]] |
| L1 | `len`/`rev` into `std/list`, retire `plusl`; `foldr`/`foldl`, `filter`, `take`/`drop`, `replicate`, `zip`, `head`/`tail`/`last` | unowned — file when scheduled |
| L2 | the absent `map` laws: `map_id`, `map_map`, `map_append`, `len_map`, `len_append`, `rev_len`, `foldr_append` | unowned — file when scheduled |
| L3 | `Mem` by recursion into Prop; the **permutation** half of `insert`/`isort` correctness. `Sorted` and the sortedness half landed 2026-08-17 in `lib/list_algos.hthr` | unowned — file when scheduled |
| L4 | permutation | unowned; forks on `count`-with-decidable-eq vs a `Perm` relation needing [[indexed-families]] |
| I | `Int` | [[std-int-encoding]] |

**Sequencing: 0 → 1 → 2 → L1 → L2, then reassess.** Waves 0, 1 and 2 landed
2026-08-16/17; the rest are writable today. L4 and any derivation-shaped
relation sit behind [[indexed-families]]; `Int` is deliberately last because it
is the stress round, not an API round.

**L3 is no longer simply "behind `Decide`", and that is wave 2's main
sequencing datum.** `Decide` landed complete over the *connectives* and absent
at the *relations*, because an instance cannot be generic over a value
([[value-generic-instances]]). So an algorithmic wave has two routes and they
have different costs: state `Mem`/`Sorted` by recursion and decide by **calling
`le_dec`/`eq_dec` directly**, which works today and is exactly what the
`list_algos` restatement does; or wait for the class to reach relations, which
wants [[value-generic-instances]] and, for anything mentioning an equation,
[[decidable-equation-carrier]]. The first route costs nothing and loses only
that the decider is named rather than found — so **L3 is unblocked**, and
whoever takes it should expect to name deciders.

## Two things this push is *for*, beyond the API

1. **Ranking the language.** The method [[list-algorithms-exercise]]
   established: write the real file, and what hurts is the ranking function
   over open issues. This round already produced two rankings before any code
   — the connectives being absent (wave 0, which no design session had
   predicted) and `Decide` being the gate on every algorithmic wave.
2. **Checking speed on realistic shapes.** `pow`/`fact` are the cheap
   instruments (large closed values on demand, feeding
   [[conversion-cost-at-large-values]] and [[numeral-stack-depth]]); `Int`
   is the realistic one. Per CLAUDE.md, none of this is a perf round unless
   its issue says so — the instruments exist to be used when one is.

## Deliberately not in scope

`div`/`mod`/`gcd`: they need non-structural termination
([[termination-measures]]) and are more valuable as a *named forcing function*
than as a fuel-shaped workaround. A division-with-remainder spec is the first
library statement that cannot be written in today's language, and that is the
datum.

## Log

- 2026-08-16: Filed. The design discussion that produced these waves also
  reversed their framing once: the first pass was Bool-first (deciders and
  `= True` reflections throughout), and the user's correction — privilege
  Prop, keep proof relevance, let the compiler do erasure — is recorded on
  [[class-ops-prop-vs-bool]], which owns it. The waves above are the
  post-correction list.
- 2026-08-16: Wave 0 landed ([[std-logic-module]], closed). Two language gaps
  it turned up have their own owners — [[false-collides-with-bools-constructor]]
  and [[exists-type-arg-not-inferred]] — and a third is a new customer for an
  existing one ([[ih-generalization]]: the Prop-first `Le` must be curried, so
  wave 1's whole kit is stated against a curried relation). Wave 1 is next and
  its dependency is met.
- 2026-08-16: Wave 1 landed except its arithmetic tail ([[nat-order-kit]],
  `docs/nat-order-design.md`). The sequencing datum it produced: the *migration*
  this push was braced for cost **nothing** — `ir_v1` and `list_algos` check
  unmodified — while the unbudgeted cost was two grammar gaps
  ([[comparison-inside-type-arguments]],
  [[quantifier-notation-in-type-arguments]]) and one wave-0 library bug. Both
  patterns argue the same way about what remains: the risk in L1/L2 is in the
  *notation and grammar* the statements need, not in restating the library.
  Sequencing unchanged; wave 2 ([[decide-class]]) is next and its `le_dec` is
  now written rather than assumed.
- 2026-08-16: Both language gaps wave 0 turned up are **fixed the same day**
  and closed: [[false-collides-with-bools-constructor]] (resolve by position,
  in two rules plus a whnf the plan did not predict — `lib/std/logic.hthr`
  now declares `False`, not `Empty`) and [[exists-type-arg-not-inferred]]
  (type arguments recovered from the value arguments' own types, first-order
  and domain-only). [[ih-generalization]] stands as the one gap wave 1 has to
  live with, and it shapes the spelling rather than blocking the work.
- 2026-08-17: Wave 2 landed ([[decide-class]], docs/decide-class-design.md). The sequencing datum it produced: Decide splits along a line the wave list did not anticipate — complete over the connectives, absent at the relations, because an instance cannot bind a value parameter ([[value-generic-instances]]). L3 is therefore UNBLOCKED rather than waiting: state the relation by recursion and call the decider by name, which is what lib/list_algos.hthr now does. The ranking this round produced, in order: value-generic instances (blocks the class from ever reaching a relation), the equation carrier key, and resolution's candidate fan-out. None was on the list before wave 2 started.
- 2026-08-17: The ranking wave 2 produced has its top item done: [[value-generic-instances]] landed 2026-08-17 (docs/value-generic-instances-design.md), the same day it was ranked. So the algorithmic-wave choice §L3 described as two routes is now one: state the relation by recursion AND reach its decider by resolution, which is what lib/list_algos.hthr does. The two remaining ranked items are unmoved — the equation carrier key, and resolution's candidate fan-out (now seven Decide instances).
