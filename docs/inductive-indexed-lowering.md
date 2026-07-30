# Indexed families, route 1: lowering by recursion on the index

Status: **scheme validated by hand prototype**, 2026-07-30 —
`crates/elab/tests/indexed_route1.rs` builds `Vec` (at an open element
code), `Fin`, and the branching `Tree` below as kernel terms and checks
them with the real kernel: §9 items 1–7 all pass, including §6.2's β on
fully open data, `append`'s definitional index arithmetic, `Fin`'s `Empty`
branch and within-class no-confusion, the branching-is-free claim of §5.1
(open-children β through `Node`, and `mirror (mirror t) = t` by induction),
and the cross-class-vacuity claim of §7 (the equations are ill-formed).
The generator is **implemented**, 2026-07-30 same day — `crates/elab/src/indexed.rs`
mechanizes §4–§6 (family, constructors, `match`), the surface forms of §2
parse (`crates/syntax`), the §3/§8.1 classification rejects with the routes
named, and `crates/elab/tests/indexed_families.rs` is §9 item 8: `append`
with definitional index arithmetic, `Fin(0)` matched as `Empty`, the
branching `mirror` with `mirror (mirror t) = t` by *surface* induction, and
the rejection list, all end to end. One hazard found by the kernel gate and
worth naming for the next reader: a family's `step` code must never be
shifted as a *detached* term — it reads its own `m`/`rec` binders as free
variables, and a bare shift moves them (`IndexedFam::at` shifts the whole
`elim_Nat` node instead). Not yet generated: `absurd`/`inj` surface forms
for indexed declarations (§7 says where they exist; nothing needed them
yet), and an indexed family as a written *type argument* (`f<Vec<Nat>(3)>`).
This was the design round for
`issues/indexed-families.md` route 1 (agreed 2026-07-28 as the near-term
scheme), written before any code per the tier discipline: a lowering bug
produces a checked theorem about a type the user did not write, the kernel
cannot catch that, and review of this document is what does. The order of
work is the tiers': this document → hand prototype against the real kernel →
generator (`docs/inductive-tier1-lowering.md` and
`docs/inductive-tier1-wf-lowering.md` are the precedents).

Conventions are tier 0's (`docs/inductive-tier0-lowering.md`): `⟦T⟧` for the
lowering of a surface type, `⌜T⌝` for a code with `El ⌜T⌝ ≡ T`, kernel names
from `crates/kernel/src/term.rs`, `Γ` the ambient context. Tier 0 §2
(monomorphized parameters, positivity posture) and §3.3 (the nominal tag)
carry over unchanged. The scheme below is
`docs/inductive-tier1-lowering.md`'s `D_ex` with one substitution — **the
user's index where the synthetic height was** — and the differences from
that document are the content here; where a rule is unchanged it is cited,
not restated.

---

## 1. What this covers, in one sentence

A declaration whose type is a family over an index, where **every
constructor's result index is constructor-headed and every recursive field
sits at a pattern variable of it** — `Vec`, `Fin`, height-indexed balanced
trees, and (once declared indices land, §8.2) subject-recursive judgments —
lowers to a type family defined by **large elimination on the index**, with
definitional β on open data and no `Id`, no `Wf`, no stored proofs, and no
coherence predicate.

The complement — result indices that are computed (`plus(m,k)`), quotiented,
or deeper than one constructor — is *not* this scheme. It fords over an
irrelevant `sEq` (route 2b, validated by `crates/elab/tests/indexed_route_2b.rs`)
and waits on that generator; here it is a **rejection with a message that
says so** (§8).

## 2. Surface form

```
inductive Vec<A> : (n: Nat) -> Type {
    Nil                              : Vec<A>(0),
    Cons(n: Nat, x: A, xs: Vec<A>(n)) : Vec<A>(Succ(n)),
}
```

- **The head** gains an index telescope: `: (n: I) -> Type`, one index in
  this round (§8.4 for more). `I` is `Nat` in this round (§8.2). The
  codomain is bare `Type`; the family's level is computed from the fields
  exactly as in tier 0, and a written `Type<n>` bound is deferred with the
  same status it has for unindexed declarations.
- **Every constructor** of an indexed declaration carries a result
  annotation `: D<params>(pattern)`, with the declaration's own parameters
  in order (the tier-1 uniformity rule, verbatim). Unindexed declarations
  do not gain result annotations; the two forms stay disjoint in the
  grammar.
- **The pattern** is one index-type constructor applied to *distinct
  constructor fields* of index type: `0`, `Succ(n)` — depth one, linear.
  `n` here is `Cons`'s own field; every pattern variable must be a field of
  the constructor (there is no other binder it could be).
- **A recursive field's index** must be a pattern variable of its own
  constructor's result index: `xs: Vec<A>(n)` under result `Vec<A>(Succ(n))`.
  That is the structurally-smaller condition, and it is what the whole
  scheme turns on.
- **Non-recursive fields** may mention pattern variables freely in their
  *types* (`p: Fin(n)` is fine). Use sites of the family
  (`Vec<A>(e)` in a `fn` signature, a field of *another* declaration, a
  motive) take an arbitrary `Nat` expression — patterns are a
  declaration-form restriction, not a use-site one.

A `record` cannot be indexed (it is tier 0 by construction, and an index
varies per constructor result — a record has one constructor and nothing to
vary).

## 3. Classification

A declaration with an index telescope is **index-recursive** (this scheme)
when all of:

1. every constructor's result index is a depth-one, linear
   constructor-headed pattern over fields of that constructor (§2);
2. every recursive occurrence is `D<own params>(x)` with `x` a pattern
   variable of that constructor's result index;
3. every field type has a code (the tier-1 restriction, unchanged — the
   family's branches are built from codes).

Everything indexed that fails 1 or 2 is **rejected, not mis-lowered**, each
with its own message (§8.1). Unindexed declarations keep their existing
tiers verbatim; the classifier's first split is "has an index telescope",
computed at declaration time like `Inductive::recursive`.

Note what is *absent* from the conditions: any bound on how many recursive
fields a constructor has. Branching is free here (§5.1).

## 4. The type

Group the constructors by the head of their result index — for `Nat`, the
`Zero`-class `z_1 … z_p` and the `Succ`-class `s_1 … s_q`. Either class may
be empty, and one index constructor may own several declaration
constructors (`Fin`'s `FZ` and `FS` are both `Succ`-class); the tag spine
within a class is tier 0 §3.2's, tag first, position taken **within the
class**.

Let `⟦c⟧` be tier 0 §3's field spine for `c` with two deletions and one
substitution:

- **pattern-variable fields are deleted** — they are not stored (§4.1);
- **recursive fields become `El rec`** — the recursion variable's code,
  spliced directly (the tier-1 rule, `docs/inductive-tier1-lowering.md` §2
  fact 2);
- **occurrences of a pattern variable in remaining field types become the
  `elim_Nat` binder** `m`.

Then

```
famD : Nat → Ty l
famD = elim_Nat^{1+l}( _. Ty l
                     ; ⌜Sum_i ⟦z_i⟧⌝                    -- index 0
                     ; (m, rec. ⌜Sum_j ⟦s_j⟧⌝)          -- index S m
                     ; · )

⟦D<ā>(e)⟧ = El^l (famD ⟦e⟧)
```

with `l = ⊔` of the field levels as in tier 0, the `elim_Nat` inlined at
each use (no kernel `def`; same cost note as
`docs/inductive-tier1-lowering.md` §7). An empty class is `⌜Empty⁰⌝` — that
is `Fin`'s `famFin 0`, and it is a *correct* branch, not a degenerate one:
it is what makes `Fin(0)` uninhabited definitionally.

There is **no Σ over the index**. `⟦D⟧` never exists un-applied; the index
lives in the type, a value of `Vec<A>(3)` is the bare payload, and `fst` of
a value is not its length — the length is the type's business. A surface
use of `Vec<A>` with no index argument is an error in this round.

### 4.1 Pattern-variable fields are index, not payload

In `Cons(n: Nat, x: A, xs: Vec<A>(n))`, the field `n` is **not stored**.
Storing it would make the `Succ` branch `Σ(n : Nat). …` — a sum over *all*
`n`, a different type — and constraining a stored `n` to equal the branch's
`m` is precisely the `Id`/`sEq` field this route exists to avoid. Instead
`n` *is* the index: the branch for `S m` types the remaining fields with
`n ↦ m`, the constructor takes `n` as a surface argument and erases it in
the term, and a `match` arm that binds `n` receives the eliminator's `m`
(§6). This is the 2b prototype's index-inversion insight in its native
habitat — there the eliminator had to *re-derive* the index by `elim_Nat`
per constructor; here the eliminator **is** `elim_Nat` on the index, so
every arm is born at the right one and the inversion machinery vanishes.

## 5. Constructors

For `c` the `i`-th constructor of its class, with result index head `Zero`
(resp. `Succ(n)` at `⟦n⟧ = e_n`):

```
⟦c(ā)⟧ = ι_i(tup(stored ā))          checked at El (famD 0)
                                     resp. El (famD (S e_n))
```

— tier 0 §4's injection and tuple over the class's spine, fed only the
stored (non-pattern) arguments, with each recursive argument's value passed
**as is** (it already inhabits `El (famD e_n)`, which is the spine's
`El rec` instantiated).

Why this typechecks with everything open: the result index is
constructor-headed by condition 1, so `famD (S e_n)` **unfolds whatever
`e_n` is** — the same "`Succ`-headed whatever the child is" argument as
`docs/inductive-tier1-lowering.md` §3.2, except the head is now supplied by
the declaration instead of computed by the constructor. No coercion, no
transport, and β under `match` fires on fully open data for the same
reason.

Constructors remain macros of fixed arity (tier 0 §4). The surface arity
*includes* the pattern-variable fields; elaboration uses them to determine
the result index and then drops them from the term.

### 5.1 Branching is free, and this is the point

`Node(l: T(n), r: T(n)) : T(Succ(n))` splices `El rec` twice:
`⟦Node⟧ = Σ(#tag). Σ(_ : El rec). Σ(_ : El rec). Unit⁰`. There is no
height to compute, no `max`, no `D_below`, no comparison to get stuck on an
open child — the failure that killed exact-height fording for branching
(`docs/inductive-tier1-lowering.md` §8.1) was that the *measure* was
computed from the children; here the index is **given by the user**, both
children sit at the same pattern variable, and `node l r` is in constructor
form with `l`, `r` open. A height-indexed balanced tree is therefore in
this scheme, branching and all, with definitional `match` β — the prototype
must pin exactly this (§9).

The general tree (`Node : T(S(max h_l h_r))`) is *not*: `max(h_l, h_r)` is
not a pattern. It fords (route 2b), or the user indexes by a bound and
lands back here. The scheme does not blur that line.

## 6. `match` and the eliminator

One construction, as in both tier-1 documents: the derived eliminator, ih
unused when the surface `match` has no self-call.

Given a motive `M` over `(h : Nat, z : El (famD h))` at level `l''`, and a
scrutinee `s : ⟦D<ā>(e)⟧`:

```
Mot(h)  = Π^{l,l''}(v : El (famD h)). M[h, v]
elim(s) = elim_Nat^{l''}( h. Mot(h)
                        ; λv. ⟨Case over the Zero-class spine⟩
                        ; (m, rec. λv. ⟨Case over the Succ-class spine⟩)
                        ; ⟦e⟧ ) s
```

In the arm for constructor `c` (in its class's case tree, binder
`x : ⟦c⟧`):

| surface binder of `c` | lowering | type |
|---|---|---|
| pattern-variable field | the `elim_Nat` binder `m` | `Nat` |
| stored payload field `j` | `fst (snd^{j+1} x)` — tier 0 §5's projection | its declared type, pattern vars ↦ `m` |
| recursive field, the `t`-th | its projection out of `x` | `El (famD m)` |

and a guarded self-call on the `t`-th recursive binder lowers to
`rec (that projection) : M[m, proj]` — the ih, one per recursive field, all
drawn from the *same* `rec` since all recursive fields sit at the same `m`.
The self-call guard is `issues/match-recursion.md`'s table-of-terms form as
in the `Wf` lowering §6.4, matching elaborated arguments against the
recursive projections.

Two composition points carry the hazard, and they are the ones
`docs/inductive-tier1-lowering.md` §4 names, minus one:

- **Arm obligation vs arm body**: the arm is written for `M[S m, ⟦c(…)⟧]`
  and owed `M[S m, v]`; convertible by `Case` β and Σ-η, with `Unit` η
  load-bearing for a nullary spine exactly as before.
- **Scrutinee instance**: `Mot(⟦e⟧)` applied at `s` gives `M[⟦e⟧, s]`
  directly. The `pair(height t; ·)` repackaging of the fording scheme is
  **gone** — there is no pair — so its Σ-η obligation goes with it. What
  remains index-side is nothing: the motive's index argument is the
  scrutinee's own index expression.

### 6.1 The surface motive over an index

The motive genuinely binds the index, and the surface must be able to say
so. The rule for `match s { … }` with `s : Vec<A>(e)`:

- if `e` is a **variable** `n`, the elaborator generalizes it: the motive
  is the goal with `n` abstracted (alongside `s` itself), and each arm's
  goal is the branch's index substituted in. This is the ergonomic case and
  covers every structural-recursion use (`append`, `map`, `head` on
  `Succ`-indexed vectors);
- otherwise the goal must not need the index refined per-arm, or the user
  supplies the motive explicitly (motives are lambdas —
  `docs/surface-universe.md`, [[motives-as-lambdas]] — so the form already
  exists: a two-binder motive `λ n v => …`).

No new inference is attempted beyond substituting a variable index; "find
the occurrences of a non-variable index in the goal" is motive inference,
and it is out of scope by the same reasoning that kept it out of
`match`-on-`Nat`.

### 6.2 What β must do, stated as the acceptance property

`match (Cons(n, x, xs)) { Cons(n', x', xs') ⇒ b }  ≡  b[n, x, xs]` with
`n`, `x`, `xs` **all variables** — the eliminator at index `S n` unfolds,
the case tree β-reduces at the injection, projections cancel against the
tuple. Same for `Node(l, r)` with both children open. This is the property
the route was chosen for and the first thing the prototype checks.

## 7. No-confusion

The index does a share of the work for free, and the rest is tier 0's.

- **Across index classes there is nothing to prove.** `Id(⟦D⟧(?); Nil; Cons …)`
  is only stateable at a common index, and `0` and `S e` head-collide — the
  *type* rejects the equation. Where tier-1 fording needed `zero_pred` and a
  `J` (`docs/inductive-tier1-lowering.md` §5.1), here disjointness across
  classes is vacuous. The prototype pins this as a negative (the equation
  fails to state), not as a lemma.
- **Within a class** (`FZ` vs `FS`, both at `S m`): inside the branch the
  type is a tier-0 sum, so tier 0 §6.1 applies verbatim — tag predicate by
  large elimination over the family (`elim_Nat` motive `Π(v). Ty 0`, the
  `is_c` shape of `docs/inductive-tier1-lowering.md` §5.2 with the height
  read replaced by the index argument), then `J` with `case = ⟨⟩`.
- **Injectivity per stored field**: tier 0 §6.2's total-projection trick,
  per class, with the recursive field's projection returning
  `⟦D⟧(m)` — no repackaging (no pair to rebuild), so the tier-1 wrinkle of
  `docs/inductive-tier1-lowering.md` §5.3 disappears. The dependent-field
  side condition is tier 0's, unchanged.
- **Index injectivity** (`Cons` at `S m` forces the tail at `m`) is not a
  lemma at all: it is the branch's typing. `issues/dependent-field-injectivity`
  stays what it is; nothing here adds to it.

A pattern-variable field has no injectivity lemma of its own (it is not
stored); equality of the *indices* is the corresponding fact and lives at
`Nat`, derived by the user from the type when needed (`S`-injectivity on
`Nat` already exists).

## 8. Rejections and deferrals

### 8.1 Rejected in this round, each with its message

- **Computed result index** (`plus(m,k)`, `max(h_l,h_r)`): "not
  constructor-headed; a computed index fords over `sEq`
  (issues/indexed-families.md routes 2b/3), not yet generated." This is the
  honest boundary: the 2b prototype measured exactly this case (open-data β
  degrades to strip-guarded there), so the message points at a measured
  fact, not a policy.
- **Deep pattern** (`Even : … Succ(Succ(n))`): needs simultaneous recursion
  (the `(D_ex, D_below)` device), a real extension — rejected with the
  pattern depth named, deferred until something needs it.
- **Non-linear pattern**: single index, so unwritable until §8.4; the check
  exists from day one anyway.
- **Recursive field at a non-pattern index** (`xs: Vec<A>(0)` under
  `Vec<A>(S n)`, or at a computed index): course-of-values in disguise —
  `rec` is the predecessor's code and nothing else exists during the
  recursion (the rejected code-tables encoding,
  `docs/branching-inductives-choice.md` §10). Rejected naming the field.
- **A pattern variable that is not a field**, or a field of non-index type
  in pattern position: malformed head, rejected at the annotation.

### 8.2 Declared index types — the stated generalization, next round

Nothing in §4–§7 is `Nat`-specific: the scheme reads "one family branch
per index constructor, `rec` at each recursive argument of the index
constructor, recursive fields permitted at any pattern variable with the
matching `rec`". A declared tier-0 enum index needs `Case` at motive
`Ty l` (exists); a declared tier-1 index needs `elim_Wf` at motive `Ty l`
(exists — the `Wf` lowering's own tag predicate uses it, §7.1 there). What
does *not* exist yet is generator plumbing for "eliminate a declared index
inside a family-of-codes" and the pattern grammar over declared
constructors — a bounded follow-on, and the reason subject-recursive
judgments (typing derivations indexed by terms) are route 1 in the issue's
2026-07-28 conjecture. This round lands `Nat`; the scheme is written so
that round is an instantiation, not a redesign.

### 8.3 Out of scope, unchanged owners

Mutual declarations (no scheme at any tier), nested occurrences
([[nested-inductives-container-fields]]), motive inference beyond a
variable index (§6.1), multi-index families (§8.4), `Type<n>` head
annotations, and the 2b generator (owned by [[indexed-families]] /
[[sprop-strict-prop]] jointly).

### 8.4 Multi-index

One index in this round. The scheme extends (recursion on one
*designated* index with the others parametric per branch — or fording the
rest), but which extension is right is exactly the kind of question that
wants a driving example, and nothing needs it yet. The grammar should not
foreclose it: the head telescope parses as a telescope even though this
round accepts length one.

## 9. Acceptance checklist (prototype, then generator)

Hand prototype first, kernel terms in `crates/elab/tests/` against the real
kernel, per the four-axis discipline of `docs/testing-generated-terms.md`
(literal *and* neutral scrutinee, open element type, checking position, a
negative control per positive):

1. `Vec` at an open element code: type, constructors, and eliminator check;
   `famVec 0` / `famVec (S e)` unfold at a neutral `e`.
2. **β on fully open data**: §6.2's property for `Cons`, at an open element
   type, in checking position.
3. `append : Vec(n) → Vec(m) → Vec(plus n m)` by the eliminator, with
   `plus` recursing on its first argument — the arm's obligation
   `Vec(plus (S n) m) ≡ Vec(S (plus n m))` is definitional; closed
   computation and an induction proof (`append xs Nil`-analogue) both
   check.
4. `Fin`: the `Empty` branch does its job (`Fin(0)` uninhabited — a
   negative), two constructors in one class, within-class no-confusion.
5. **Balanced tree**: `Node` with two children at the same pattern
   variable; β with both children open; a `mirror`-style induction.
6. Pattern-variable recovery: an arm binds `n` and gets the eliminator's
   `m`; a proof that uses it checks.
7. Negatives: mismatched index rejects (`Cons …` against `Vec(0)`;
   a value at the wrong index in checking position); the cross-class
   equation fails to state; and the §8.1 rejections each fire with their
   message (generator phase).
8. Generator phase adds: the nominal tag, multi-constructor classes beyond
   two, fields at levels above 0, and the surface forms end to end
   (declaration, constructors in expressions, `match` with self-call,
   `absurd`/`inj` where §7 says they exist).

What the checklist deliberately repeats from `tier1_fording.rs`: nothing —
that suite stays the height-fording stress record; this scheme's prototype
is its own file, and the overlap (`List`-shaped spines) is the unindexed
tier's business, not this one's.

## 10. Known seams, recorded at landing

Not defects — every one is tested around — but each is a place where a
future change breaks *this* scheme first, so they are written down here
rather than remembered.

1. **`indexed_of` is a structural fingerprint.** The family form is
   recognized by shape — `El (elim_Nat(_. Ty l; …))` with a nominal-tag
   code read out of a branch. It is the indexed analogue of `tag_of`, but
   the pattern is far bigger, so it is far easier to break *silently*: any
   pass that normalizes or restructures emitted terms (a kernel `def`,
   level canonicalization à la `normalize_levels`, hash-consing that
   rewrites) makes every indexed type unrecognizable, and the symptom is
   "not in the family form" errors far from the cause. If such a pass
   lands, this recognizer is the first consumer to re-audit.
2. **Type identity depends on presentation.** A family type that arrives
   *pre-reduced* (whnf'd at a literal index, upstream of the consumer) has
   lost its index, and constructors/`match` against it are diagnosed, not
   handled. Declared types flow through unreduced today, so the gap is
   theoretical — but it is a semantic wart, and the fix when something
   hits it is a re-synthesis path (rebuild the family from the declaration
   and convert), not a better message.
3. **Term size.** The whole family `elim_Nat` is inlined at every type
   occurrence and re-instantiated several times per eliminator — the tier-1
   cost note (`docs/inductive-tier1-lowering.md` §7), amplified, because
   indexed types appear *in other types*. Acceptable now; a kernel `def`
   is the eventual fix, and [[frontend-benchmarks]] is where "acceptable"
   gets a number.
4. **The arm walk exists twice.** `indexed_case_tree`/`elab_indexed_arm`
   mirror `case_tree`/`elab_arm` deliberately (threading the pattern
   variable and the guard through the shared walk would couple what the
   tiers keep separate), which means two places must agree on the
   projection-annotation discipline. A *third* variant is the signal to
   extract the walk, not to copy it again.
5. **Uniformly-level-0 tests cannot see a dropped join.** The
   `fields_above_level_zero` test exists because everything else in the
   acceptance suite lives at level 0, where `l ⊔ mlvl = mlvl` hides a
   wrong level annotation. It caught two real bugs on its first run: the
   eliminator's `elim_Nat` level must be the motive Π's level (the join),
   and a universe expected type can hide under `El` of a quoted code
   (`elab_check`'s type-position bridge now reduces before giving up —
   the components of an indexed spine are exactly such `El (TmTy …)`s).
   The rule this generalizes to: every new consumer of the family form
   keeps one nonzero-level case in its tests.
