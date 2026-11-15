# Segment maps: what Pottier's fast thinnings mean for Heather

Status: **survey**, 2026-10-25. Source: François Pottier, *Fast thinnings via
segment maps* (preprint for the Journal of Functional Programming, 2026,
<https://cambium.inria.fr/~fpottier/publis/fpottier-segmap.pdf>), committed
beside this note as `docs/papers/fpottier-segmap.pdf`. Section and figure numbers
below are the paper's. Follow-up is in §7. Read against master at `e36a275`.

The paper is about one data structure, so, like the definitional-inversion
survey (`docs/definitional-inversion-survey.md`) and unlike the Arend survey
(`docs/arend-survey.md`), most of Heather's areas have nothing to take from
it. Its bearing is on one question the kernel has met several times and
deferred each time: **should Heather's terms carry suspended renamings, and
if so, how should a suspended renaming be represented?** The paper answers
the second half carefully and says outright that it does not answer the
first (§1.1, §5.2).

---

## 0. The answer in brief

1. **Every thinning Heather suspends today has weight zero or one, so the
   paper has nothing to accelerate now.** The lazy global offset
   (`docs/lazy-global-offset-design.md`) is a pure `north k` (one half-line,
   weight 0) and its invariant (I) materializes the one case that would need
   a cutoff. Every `shift_*_above(by, cutoff)` in `subst.rs` is
   `northeast cutoff ∘ north by`, weight at most 1. The local namespace in the
   value machine uses levels and never shifts at all. Segment maps start to
   pay only when long chains of cutoff-shifts are composed and kept, and
   Heather keeps none.
2. **The one place it would matter is the representation change Heather has
   deferred.** `issues/open-payload-shift-copies.md` and the module docs of
   `crates/kernel/src/subst.rs` name "shift-annotated or hash-consed terms" as
   the fix for open payloads deep-copied under binders, and keep it deferred
   because the trigger has not fired (local substitution is about 4% of the
   last profile). If it is ever taken, this paper is the reference for the
   annotation's *data structure*: its composition with a short shift is
   `O(log W)` (§4.6.3), which is exactly the cost of pushing one binder's
   shift onto an accumulated renaming.
3. **It does not remove the reason the change is deferred.** The danger the
   issue names is that an explicit-shift node either reduces away before code
   observation or becomes observable syntax, and Heather's `□` conversion,
   the elaborator's strengthening and zonking tests, and the bounds memo all
   rely on structural `==` of terms. The paper's own segment maps lack
   canonical equality (§3.5); the alternative it sketches there does have it,
   but canonical thinnings are necessary and not sufficient: `t[ρ]` and
   `t'[ρ']` can still denote the same term. A Heather design would have to
   push shifts to the leaves (or normalize them away) before any `==`.
4. **One cheap idea transfers to the value machine independently:
   environment lookup.** Rocq's kernel represents explicit substitutions as
   Okasaki skew binary random-access lists (§5.1, citing Pédrot's design).
   Heather's `value::Env` is a persistent linked list whose lookup costs the
   de Bruijn index. A random-access list keeps `O(1)` push and shared tails
   and makes lookup `O(min(i, log n))`, never worse. Whether deep lookups
   happen at all is unmeasured; the cheap step is a counter, filed as
   `issues/env-lookup-depth.md` with no puller.
5. **Heather's experience answers two of the paper's open questions**, which
   may be worth telling the author: tracking each subterm's maximum free index
   pays a lot (`bounds.rs`, 7.9× on the ir_v1 check), and it pays as a memo
   keyed by allocation rather than as a field; and a suspended offset that
   composes uniformly is enough to remove the rescoping copy from the hot
   path, once materialization is pinned to the points where syntax is
   observed (§5).
6. **Native compilation is not a customer.** FunctionIR uses stable value IDs
   precisely to avoid index shifting (`docs/function-ir-design.md` §6.2–6.3),
   and the x86 lowering's label arithmetic is constant offsets. A verified
   segment map *written in Heather* would be a reasonable `lib/std/data`
   exercise (§6), but no milestone pulls it.

---

## 1. What the paper contributes

A **thinning** is an increasing function `ℕ → ℕ` (McBride's `m ⊑ n`, with
constructors `Done`, `Keep`, `Drop`). In a de Bruijn system, thinnings are
the renamings that weakening produces: "shift by `k` above cutoff `c`" is one,
and so is any composition of such shifts.

Pottier represents a thinning of **finite extent** (diagonal beyond some
point) as a sequence of diagonal *segments*, each an altitude (`gap`) and a
length (`len`), ending in a half-line. Its **weight** `W` is the number of
segments: the number of discontinuities. A plain segment list already
compresses runs of `Keep` and `Drop`; the paper's step is to store the
segments in a skew binary random-access list (Okasaki 1999, §9.3.1), with two
extra tricks:

- every `Node` and every spine `Cons` carries a pending vertical
  displacement (`gap`), so moving a whole map or tree north is `O(1)`;
- adjacent segments that could be fused must be fused (the `minimal`
  invariant, Fig. 12–13), so a map has the fewest segments its function
  allows.

The operations and their costs (§1.3, §4):

| operation | meaning | cost |
|---|---|---|
| `identity` | `x ↦ x` | `O(1)` |
| `north j` | add `j` to every image | `O(1)` |
| `east a d` | prepend a segment of length `d` at altitude `a` | `O(1)` |
| `northeast d` | move under `d` binders | `O(1)` |
| `view` | pop the first segment | `O(1)` |
| `get` | lookup | `O(min(1+s, log W))` |
| `invert` | least `x` with `y ≤ get x` (reverse lookup) | `O(min(1+s, log W))` |
| `west d` | drop the first `d` indices | `O(min(1+s, log W))` |
| `compose` | `get (compose m₁ m₂) x = get m₂ (get m₁ x)` | `O(W₁+W₂)`; `O(log W₂)` if `m₁` has `O(1)` extent, symmetrically |
| `equal` | extensional equality | `O(W)` (shape is unique per weight) |
| `prune x` | forget everything past `x`, imprecisely | `O(log W′)` |

The composition algorithm is the paper's centre: iterate over whichever map
is lighter, cutting slices out of the heavier one with `west` and gluing them
with `clip` (Fig. 19), with an amortized argument over sequences of cuts
(§4.3–4.4). The Rocq implementation is verified for functional correctness;
termination of `compose` uses fuel proved sufficient afterwards, because
well-founded recursion would have needed the well-formedness invariants at
definition time (§4.6.3). The complexity analysis is informal, and there is
**no empirical evaluation** (§5.2).

What it does not do, by its own account (§1.1): decide which nodes carry a
renaming, when to compose versus apply, whether to memoize, or how to prune.
Those are the questions a kernel actually has to answer.

## 2. Where Heather has thinnings today

| site | thinning | suspended? | weight |
|---|---|---|---|
| `subst.rs` `shift_local`/`shift_global`/`shift_univ` (+`_above`) | `x ↦ x` below the cutoff, `x + by` above | no, eager copy (local namespace skips closed subtrees via `bounds.rs`) | ≤ 1 |
| `value::Env` locals | none: variables are levels, pushing a binder renumbers nothing | n/a | n/a |
| `value::Env::gshift` (lazy global offset) | `x ↦ x + k`, cutoff 0 by invariant (I) | yes, one `u32` | 0 |
| `value/shift.rs` (conversion's telescope weakening) | `+univs`, `+globals` | eager on values; a `Syn` closure's body becomes `gshift += g` | 0 |
| `reduce::GlobalCache` signature rescope | `shift_global(v + 1)` | memoized per index, rebuilt at `push_tele` | 0 |
| `module_relocate.rs` (moving module images) | old dependency position ↦ new, partial | applied once per payload by `reindex_global` | arbitrary |
| `unification.rs` `strengthen_tm`/`drop_binders` | inverse of `north d` (drop the innermost `d`) | no, substitute then compare | 1 |

Three observations.

**The suspended ones are all weight 0.** A constant offset composes with
another by addition, and the lazy-offset design says so ("uniform cutoff-0
shifts compose", §5). A segment map of weight 0 is a single `Id gap`; all its
machinery is idle.

**The eager ones are weight ≤ 1, and their cost is the term, not the
renaming.** `shift_local_above(by, c)` is `get x = if x < c then x else x +
by`, that is `northeast c (north by identity)`. Looking it up is a compare
and an add. Their cost is the copy of the subtree, which `bounds.rs` already
avoids for subtrees with no free variable at or above the cutoff.

**Cutoffs are where a weight-0 representation stops.** Invariant (I) of the
lazy-offset design exists because a pending offset carries no cutoff: a
closure whose body sits under a global binder is built with its offset
already materialized (`shift_global_above(k, 1)`). A weight-1 thinning would
represent that case lazily. The design materializes there anyway for a
different reason (trap 2: boxes carry raw syntax and compare by `==`, and
`letbox`'s β must not meet an eager box inside a lazy body), so a richer
offset type alone would not let those six sites go lazy.

## 3. The one place it would matter: shift-annotated terms

`issues/open-payload-shift-copies.md` (open, kernel) owns the last way a
single substitution can cost more than the paths to its variables: an
*open* payload substituted under `k > 0` binders is `shift_local(k)`-copied
per occurrence. It names two fixes, explicit-shift nodes and hash-consing,
and defers both: the trigger is a profile where these copies dominate a real
workload, and the last measurement had all local substitution at about 4%.

If that trigger ever fires, the design has to choose a representation for
the shift annotation. What the paper settles for that design:

- **Annotations will compose, and the composition that happens is lopsided.**
  Substituting under one more binder composes a weight-1 shift onto whatever
  the payload already carries. With segment maps that is `O(log W)` (the
  `O(1)`-extent case of §4.6.3), against `O(W)` for a segment list and
  `O(n)` for a bit vector. Nested binders under nested substitutions are
  exactly the inlined-interpreter workload that made `bounds.rs` worth 7.9×.
- **Lookup during evaluation is `O(log W)`**, and `is_identity_below x` is
  `O(1)` (§4.7), which is the test "is this annotation trivial on this
  subterm's free variables" that would let a traversal drop it.
- **`prune` is the bounds memo's partner.** Given a subterm's maximum free
  index (already memoized), `prune` discards the part of the annotation the
  subterm cannot observe, in `O(log W′)`. That keeps annotations from growing
  with the depth of the context rather than the variables actually used.
- **A weight comparison chooses the cheap side.** The hybrid composition is
  never worse than either one-sided algorithm, and the weight query is `O(1)`.

What the paper does not settle, and what remains the real decision:

- **Structural equality.** Heather's `□` conversion is syntactic `==` modulo
  level equivalence (`crates/kernel/DESIGN.md`, the invariant behind both
  equality observers over codes). The elaborator's `strengthen_tm`,
  `zonked`, `zonked_tm` and `mentions_binder` decide scoping by substituting
  markers and comparing with `==`. The bounds memo is keyed by allocation. An
  explicit-shift node breaks all of these unless every observation point
  pushes shifts to the leaves first. Pottier's segment maps are not canonical
  (the `Cons` `gap` field, §3.5); his proposed fix (store each node's height,
  drop the `gap` on `Cons`) makes the *map* canonical, since the skew binary
  shape is unique per weight. But two annotated terms can denote the same
  term with different annotations at different depths, so canonical maps
  only make the push-to-leaves normalization deterministic; they do not
  replace it.
- **Code observation.** The code recursors see syntax. A shift node is either
  pushed away before a `box` is observed (so layer c never sees one, which is
  the lazy-offset design's choice for boxes) or becomes a constructor of
  `Code` with its own recursor branch, which the issue rightly calls the
  dangerous option.
- **Whether it is worth it at all.** Pottier is explicit that segment maps
  versus bit vectors versus plain segment lists is an open empirical
  question that depends on typical weights and extents (§5.2). Heather would
  have to measure that on its own workloads, with `scripts/perf ab`.

So the paper changes the cost estimate of one candidate in the issue, not the
trigger or the decision. It is logged there.

## 4. Environments as random-access lists

The paper credits Rocq's kernel (`esubst.ml`, Pédrot's design, written up by
Bouverot-Dupuis 2026) with storing explicit substitutions in a skew binary
random-access list (§5.1). Heather's analogue is `value::Env`: a persistent
singly linked list in the query arena, where `lookup(i)` walks `i` nodes.

- A skew binary random-access list keeps what `Env` relies on: `O(1)` push,
  persistence, and sharing of the outer part between closures, so head-pointer
  identity of a spine (`Env::ptr_eq`, `Env::ident`) still means "same
  environment". Lookup becomes `O(min(i, log n))`, so it is never
  asymptotically worse; the costs are a tree node per pair of entries and a
  slightly more involved `values_ptr_eq_prefix`.
- Whether any workload looks up deep indices is unknown. The evaluator's
  `value-metrics` counters record `env_nodes` (pushes) but not lookup steps.
  Short binder telescopes (the recursor steps bind at most seven) do not
  care. Long ones might: a big `let` block, a function with many parameters,
  the native `Straight` stretches that carry every variable of a run.

Per `docs/roadmap.md`, kernel work waits for a puller and per `CLAUDE.md`
perf work starts from what the corpus says dominates. So this is filed as an
accumulator with a measurement first: count lookup steps beside `env_nodes`,
and look at the distribution on `scripts/perf report`'s corpus. It is worth a
round only if lookups beyond a few dozen steps show up as a visible share.

## 5. What Heather's experience says back

The paper lists questions it does not answer (§1.1). Heather has answered two
of them on its own workloads, and the answers may interest the author:

- *"Should every subterm keep track of … its maximum free de Bruijn index, so
  that the domains of renamings can be pruned? What is then the cost?"*
  Yes, and it changes asymptotics, not constants: disabling `bounds.rs`'s
  skip hooks costs 1.47× on a routine check and turns a benchmark's scaling
  slope from 0 to 1 (`crates/kernel/DESIGN.md`, Representation). It is kept
  as a memo keyed by allocation, not a field on each node, so construction
  sites need not maintain it; the price is a measured tax on one-shot
  checking (`issues/bounds-metadata-taxes-one-shot-checking.md`).
- *"Which nodes should carry a renaming?"* In Heather, closures (syntax paired
  with an environment) carry the global offset, never term nodes; it is
  materialized exactly where syntax leaves the value path (boxes, code, the
  rewriter). That removed the rescoping copy from the hot conversion path
  without touching the term language. It needed only weight-0 maps because
  locals are levels in the value domain and never shift.

## 6. Heather in Heather and the library

- **Native compilation and FunctionIR**: not a customer. The IR deliberately
  uses stable value IDs rather than positional references, because
  positional references "cause index shifting under insertion and deletion"
  (`docs/function-ir-design.md` §6.2–6.3). Program placement lemmas
  (`runs_weaken` by a program length) shift labels by constants.
- **Moving module images** (`crates/elab/src/module_relocate.rs`): the
  position map is in general partial (a dependency with no counterpart
  refuses) and is applied once per payload, so there is no composition to
  speed up. When an upstream module only *grows*, the map is a thinning of
  small weight (one segment per insertion point), and a segment list would be
  its natural description, but the map's cost is not visible anywhere.
- **A segment map written in Heather.** The Rocq development is small and
  verified, and porting it would exercise things Heather is still building:
  integer arithmetic with `omega`, nested well-formedness invariants on a
  persistent structure, and the choice Pottier faced for `compose`: a
  `decreases` measure (`min(W₁, W₂)`, which needs the invariants at
  definition time) or fuel proved sufficient afterwards. Fuel is also the
  form `compile-x86` turns into a verified loop today; measure recursion is
  `issues/function-ir-loop-measure-recursion.md`. It would also be a
  candidate first persistent structure for `hih-first-alloc` once native
  programs can allocate. Nothing pulls it now, so it is noted here and not
  filed.
- **Tactics and the kernel model**: Heather tactics reach terms through the
  host interface, not as de Bruijn syntax they rename themselves, and the
  kernel model (`lib/kernel_model/kernel_reduction.hthr`) is locally closed
  where reduction opens a binder, so it never shifts. Neither needs thinnings.

## 7. Follow-up

- **Logged** on `issues/open-payload-shift-copies.md`: if the representation
  change is taken, segment maps are the candidate annotation structure, with
  canonical form (§3.5's variant) and push-to-leaves before every `==` as
  the price.
- **Logged** on `issues/signature-rescope-multiplicity.md`: its candidate 1
  (thread `gshift` through `Conv::subst`) stays weight 0; a cutoff would need
  a weight-1 offset, and §2 of this note is why that alone does not make the
  boxed sites lazy.
- **Filed** `issues/env-lookup-depth.md` (kernel, no milestone, no puller):
  count environment lookup steps, and consider a random-access-list `Env` only
  if deep lookups show up.
- No language, tactic, mathematics or export follow-up.
