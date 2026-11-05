---
title: Corecursion up to friends, round 2 (indexed, polymorphic, bind-shaped)
status: open
labels: [codata,coinduction,elaborator]
area: interaction-trees
created: 2026-11-02
updated: 2026-11-03
milestone: [nh-effects]
---

Corecursion up to friends landed for unindexed codata and monomorphic
friends (`docs/codata-elaborator-design.md` §5.5): the carrier is the free
algebra of the friends over seeds and existing trees, a `Wf` tree, and each
friend's body is re-elaborated over it. The issue's three customers need
more than that:

- **Up-to proofs for `Bisim`/`Eutt`** (`docs/coitree-design.md` §7.6): a
  self-call under `trans`. Indexed codata: the free carrier becomes a family
  over the index (`Wf` → `IWf`, or a seed-style equation per node), and a
  friend's codata arguments sit at *different* indices from its result
  (`trans(r₁ : Bisim(a, b), r₂ : Bisim(b, c)) : Bisim(a, c)`), so the node's
  shape must carry the intermediate index `b`.
- **A direct coinductive `rec`** (`docs/partial-functions-design.md`):
  the non-tail call sits under `bind(t : CoTree<R>(E), h : R → CoTree<S>(E))`.
  `t` is of another instance than the result (the free carrier becomes
  multi-sorted: a node of `C_R` may hold children of `C_S`), `h` is a
  function into codata (a function-indexed child, so `Wf`'s `Vec` children
  no longer suffice), and `bind`'s `Ret(r) => h(r)` returns a *child's* node
  rather than an argument's, which `Wf` recursion supports (the child's `ih`
  is in hand) but friend mode refuses today.
- **Power series generic over a ring** (`issues/formal-power-series.md`):
  a friend `add<A: CommRing>` has a type parameter and a class binder.
  Friend mode would instantiate the friend's type parameters from the
  definition's codata type and its class binders by resolution at the call.

Smaller gaps, each refused with its reason today:

- friends whose parameter types mention other parameters (`E: Events` before
  `t: CoTree<R>(E)`);
- a friend calling another friend in its own step (the free algebra already
  has every friend's node; friend mode would accept a call to any friend of
  the site at a child);
- constructors nested above a call beside a friend (§5.4 with §5.5: a
  pending-node shape in the free algebra);
- a constructor with a call inside a friend's argument (the same pending
  node, as a leaf).

## What it assumes from elsewhere
- **`docs/codata-elaborator-design.md` §5.5** owns the round-1 carrier and
  friend mode. Assumed here: only that the step is structural recursion on
  the free carrier and friend nodes read their arguments' nodes from `ih`.

## Log

- 2026-11-03: The up-to proofs for `Eutt` (up to `trans` and up to `bind`) are now wanted
  by `nh-effects`: [[eutt-iteration-and-io-reading]] states its loop lemmas
  first and logs which proofs wait here, and [[eutt-tactics]] builds its
  coinduction tactic on them (`docs/effects-capabilities-design.md` §4).
- 2026-11-03: 2026-11-03: [[eutt-iteration-and-io-reading]] closed with every lemma proved by direct corecursion (iter_cong, mrec_cong, mrec_bind, reads_bind, the loop lemma reads_iter): where a self-call would sit under trans, the hypothesis is generalised to the relation the step lands in (docs/coitree-design.md §7.9, docs/proof-patterns.md §4). nh-effects no longer waits on up-to Eutt; eutt-tactics still wants it for an ecofix-style tactic.

## Log

### 2026-11-03: round 2 landed (docs/codata-elaborator-design.md §5.6)

The free carrier is an ordinary `W` over seeds, trees, pending nodes and
friend labels, with an `ok` predicate that every node sits at the index its
parent wrote. Done:

- **indexed friends**: `sb_trans` (friend's arguments at other indices than
  its result) carries coinduction up to transitivity on a bisimilarity;
  a friend at the wrong index is refused at the call;
- **function-valued codata arguments** (`h : Nat → Dl`), read one layer at
  an application (`match h(n)`) or returned (`Now(n) => h(n)`), as `bind`
  does; a whole function child passes as its η-expansion;
- **polymorphic friends** and parameters whose types mention earlier ones
  (`E: Events` before `t: CoTree<R>(E)`): type parameters fixed by the
  result are the definition's, the rest are data written at the call;
- **constructors nested beside a friend** and a constructor with a call
  inside a friend's argument (pending nodes);
- **friend calls inside a friend's argument** in the definition;
- the library: `Eutt::up_to_bisim` and `Eutt::bind_up` (with
  `Bisim::after`, `CoTree::bind_ret_at` for exact counts), and the loop
  congruence proved through both in `lib/_tests/std/itree/coitree_eutt_tests.hthr`
  (`iter_cong_up_to`; the library's `Eutt::iter_cong` is direct, PR #409).

Left (each refused with its reason):

- **a friend at the top of the body**, not under a constructor. Wrapping the
  goal in `CTau` on both sides and peeling it with `tau_l`/`tau_r` works
  today (`iter_cong_tau`); supporting it directly needs the seed's step to
  run a friend node over a fresh tree, a second level of carrier.
- **friends calling other friends** in their own bodies;
- **class binders** on friends (series over a ring), resolved at the call;
- **a child at another instance** of the family (`bind`'s `t :
  CoTree<A>` under a `CoTree<B>` result) for a direct coinductive `rec`: a
  multi-sorted carrier;
- type arguments for a friend's data type parameters are not inferred from
  its data arguments; the call writes them.

Found on the way, not a friends gap: [[corec-match-on-index-term]].
- 2026-11-05: gardener: cites a file it shares with [[coitree-rec-program-bridge]] (`docs/coitree-design.md`); [[kernel-coinductive-types]] (`docs/codata-elaborator-design.md`); [[partial-functions-coinductive]] (`docs/coitree-design.md`).
