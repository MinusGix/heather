# Synthesizing a `match`'s motive from the goal

Design doc for `issues/goal-motive-by-scrutinee-abstraction.md` (ranked #1 by
waves L2′/L3, ten sites) and `issues/nested-match-on-field-binder-motive.md`
(ranked #1 by the `Int` round, fourteen sites), landed 2026-08-17. The claim
being designed: a motive-less `match` in checking position should recover the
dependent motive whenever the goal *is* about the scrutinee — not only when it
is about a variable, and not only when it says so without reducing.

The second issue's hypothesis was that the two are one defect. **They are one
defect in the sense that matters** — one function, `Elaborator::synth_motive`,
with one guard too strong (`Term::Var`) and one step missing (reduce the goal)
— but they are **two mechanisms**, and neither fix subsumes the other. §2 is the
evidence, because the coordinator's merge decision rests on it.

## 1. What the synthesis is

`match e { … }` at expected type `T` elaborates to an eliminator, and an
eliminator needs a motive `M` over `Γ, z : S` with

    M[e/z] ≡ T

The arms are then checked at `M[cᵢ/z]`, which is the whole point: that is where
the goal *specializes* to the branch the arm picked, and where `filter`'s two
arms stop being the same statement. A motive is therefore never wrong in the
soundness sense — the kernel re-checks the obligation — but a motive that is
too weak leaves arms that nobody can close, including by `{}`.

The old synthesis was one move: if `e` elaborates to `Var(x)`, swap `x` for `z`
in `T↑¹`; otherwise hand back `T↑¹` unchanged, the non-dependent motive. The
swap is `[x ↦ z]` as a `LocalSubst`, so the obligation holds by construction.

## 2. Two mechanisms, one function

**Mechanism A — the goal names the scrutinee, one unfolding later.** In
`filter_append`'s `Cons` arm the goal is

    filter(append(Cons(h, t), ys), p) = append(filter(Cons(h, t), p), filter(ys, p))

and the split is on `p(h)`, which occurs *nowhere* in it. It occurs in what the
goal reduces to: `filter(Cons(h, t), p)` steps to `match p(h) { … }`. Nothing
about variables is involved — `p(h)` is not one, and could not be.

**Mechanism B — the scrutinee is a projection, and the goal names the value it
was projected out of.** A tier-0 arm binds its fields as *aliases*: `n` in
`match b { Wrap(n) => … }` is the term `fst(snd b)` (`inductive.rs`,
`elab_arm` — the kernel has no `let`, so each use is the projection). The arm's
goal, meanwhile, is the outer motive at the arm's **value** `v`: `ddb(v) = v`.
So the field does not occur in the goal *at all*, before or after reduction,
and abstracting it — the second issue's proposed fix, taken literally — finds
nothing. Measured, 2026-08-17: with occurrence-of-the-scrutinee abstraction and
goal reduction both in place, the `Box` repro still failed. What the goal needs
is the opposite move: replace `v` by the *constructor value rebuilt around* `z`,
`⟨tag, z, ⟨⟩⟩`, which is exactly what the hand-written motive
`λ y => ddb(Wrap(y)) = Wrap(y)` says.

So the merge is justified — one function, one round, one doc — but the fix is
two rungs and the issues' shared "abstract the scrutinee term rather than a
`Var`" sentence is only half of it. This is recorded rather than smoothed over
because the half that is missing is the one that costs fourteen sites.

## 3. The kernel operation

`Type::abstract_local(pat)` (`crates/kernel/src/subst.rs`) is the inverse of a
singleton substitution: `T` weakened into `Γ, z`, with every occurrence of
`pat` replaced by `z`, or `None` when there is no occurrence. Two variants:
`abstract_local_with(pat, rep)` plants a term *containing* `z` instead of `z`
(mechanism B), and `abstract_local_any(pats)` abstracts several spellings of
one term to the same `z` in one pass (§4.4).

Three decisions:

1. **In the kernel, on the existing traversal.** Binder bookkeeping — which
   field of which node is under how many binders, in each of the three
   namespaces — lives in exactly one place (`subst.rs`'s module doc), and a
   second copy in `elab` is the kind of thing that is right for a year and then
   silently wrong for one node. The traversal gained one hook, `Mapper::pre_tm`,
   which replaces a whole term node before its children are visited; it defaults
   to `None`, so every other mapper is unchanged and monomorphizes it away.

2. **"Occurrence" is `==`**, structural equality on de Bruijn terms, which is
   α-equality here. Same decision and same reasons as `lgg.rs`'s anti-unifier:
   no conversion call inside the walk, so the walk is linear and terminating.
   Where conversion *is* wanted it is applied to a handful of candidates
   chosen first (§4.4) — never at every node.

3. **`None`, not the constant motive.** "There is nothing to abstract" and
   "here is a motive" are different facts, and every caller wants to try
   something else before settling for the constant one.

**Why the obligation survives.** `abstract_local` only ever replaces a position
that literally held `pat`, so `M[pat/z]` is `T` again, syntactically —
*whatever* subset of the occurrences the walk found. Partial abstraction is
therefore always sound; it is only ever *weak*. The two rungs that reduce
something (§4.3, §4.4) and the rebuild of §5 weaken this to "≡ up to
conversion", which is what the kernel checks anyway.

## 4. The ladder

`synth_motive` tries, in order, and returns at the first rung that finds an
occurrence.

### 4.1 The goal as written, scrutinee as written

The old `Var` case, generalized to any term and subsuming it exactly: for
`pat = Var(x)` the abstraction *is* the old swap substitution. Every motive
this synthesis has ever recovered is this rung, it costs one traversal and no
reduction, and no program that checks today gets past it. That is the answer to
"when do we whnf": **not on the path anything working takes**.

### 4.2 The goal as written, scrutinee re-read as a field (§5)

Also cheap — the re-read is a walk down the projection path of the scrutinee
itself, not of the goal — and also no reduction.

### 4.3 The goal reduced

`expose` puts the goal's **exposed term positions** in weak head normal form.
Type-level `whnf` alone does nothing to an equation: `Id` *is* a head, and
everything worth unfolding sits in its two sides. So the sides are reduced too,
as is an `El`'s code and an implication's *domain* — `Mem(a, filter(xs, p)) -> …`
is the shape half the `Mem` kit proves in, and its computation is all in the
domain. A codomain is not exposed: it lives under a binder, and a scrutinee
scoped in `Γ` cannot occur there unshifted.

This is one layer, not a normalization. Anything deeper is unbounded, and it is
not needed: the arms are checked up to conversion, so an occurrence the
abstraction misses costs specialization at that position and nothing else.

### 4.4 …and matched up to conversion, at the positions it is stuck on

The syntactic pass over the *reduced* goal is not enough, and the reason is
worth stating because it is what a "just whnf the goal" fix gets wrong.
Reduction **respells**: unfolding `filter(append(Cons(h, t), ys), p)` rebuilds
the cons cell, so the `p(h)` the left side is blocked on is `p` applied to a
projection *of a literal pair* — one Σ-β step from the `p(h)` the elaborator
built for the scrutinee, and not the same term. The right side, whose `Cons` is
the original, spells it exactly. Measured, 2026-08-17: syntactic abstraction on
the reduced `filter_append` goal hits the right side and misses the left.

Half an abstraction is worse than none. The arms then face a goal specialized
on one side and stuck on the other, which no arm can close — and it *looks*
like the fix worked everywhere else.

So the reduced goal is matched by **conversion**, at the positions it is stuck
on: the scrutinee of an eliminator that could not fire, recursively, plus the
same under the constructors and applications that can wrap one
(`stuck_scrutinees`). That candidate set is small — a handful of positions, and
capped at `STUCK_CANDIDATES` — which is what makes a conversion call per
candidate affordable. It is also the *right* set: what a `match` is splitting
on is what its goal is blocked on. Everything that converts is abstracted in
one pass (`abstract_local_any`), so every spelling becomes the same `z`.

### 4.5 The goal read below its binders

`issues/case-split-on-a-definitions-tests.md`, 2026-11-11. §4.3 reads one
layer and no codomain, which is right for an equation and leaves out the
goals a relation or an `↔` unfolds to. `Regex::alt(a, b) ≈ Alt(a, b)` is,
reduced, `Π w. (alt(a, b).Denotes(w) → …) × (… → alt(a, b).Denotes(w))`:
every position stuck on `a.is_no_match()` is in a codomain or a component.
With no rung reaching them, `match h: a.is_no_match()` left the arms the
goal as written, and each such definition was written twice, once with its
tests as parameters (`alt_at`), so that a theorem could take them apart as
variables.

The last rung, tried only when every rung above found nothing
(`abstract_below`): each former is reduced in its own context, through `Π`
codomains and `Σ` components to a fixed depth; the positions each reduced
term is stuck on are collected as §4.4 collects them and brought back to
`Γ` by strengthening, so one that mentions a binder it sits under is no
candidate; those that convert to the scrutinee are abstracted, all at once,
in the reduced goal. The motive's instance at the scrutinee is the goal
reduced, which converts to the goal, and the kernel is asked as for every
other rung.

**It changes proofs that were written for the constant motive.** Where no
rung found anything, the arms used to keep the goal as written, and a proof
could be written against that: prove each arm about the unreduced call, by
a lemma that takes the arm's evidence (`t.assoc_get_hit(row, k, hit)`).
Once this rung specialises the goal, such an arm no longer has the arm's
type. Three library proofs were of that kind (`Bisim::after`,
`List::assoc_get_present`, `StructuredRegion::loop_settles`) and were
found only after the rung merged, because the PR lane replays unchanged
library modules after a compiler edit. They are rewritten to the
specialised goal, which is shorter, or pinned with `as λ _ => …`. A change
to this ladder is verified by re-elaborating every library module, not by
the PR lane alone. In all three the elaborator accepted the old arm and
only the kernel refused it
(`issues/match-arm-accepted-against-unspecialised-goal.md`).

§4.3's objection to codomains was scope: a scrutinee scoped in `Γ` does not
occur under a binder unshifted. The abstraction shifts its patterns as it
descends, so the objection is to the *candidates*, and strengthening
answers it.

What it does not reach, each pinned as a refusal in
`lib/_tests/std/core/match_motive_below_tests.hthr`:

- a test that mentions a binder of the goal (split where the binder is in
  scope);
- a call that is the argument of a variable head, `P(pick(n, a, a))`:
  that is a weak head normal form, and nothing is stuck;
- a call that is an argument the reduction is not waiting on:
  `k.leb(pick(n, a, a))` is stuck on `k`, so `pick`'s test is not a
  position anything is stuck on. Reading it would mean normalising the
  arguments of every neutral term in the goal
  (`issues/case-split-reaches-arguments-of-stuck-calls.md`). Until then
  the theorem is stated at a name, `(p: Nat) → p = pick(n, a, a) → …`,
  where the equation is a position of its own;
- a call in a summand of a disjunction, `f(n) = a ∨ f(n) = b`. Reading
  summands was tried and taken back out: the reduced goal replaces a
  defined type whose unfolding is a sum by that sum, and a proof that
  builds it by its constructors (`BRet(…)` at `Bisim`, in
  `lib/std/itree/coitree.hthr`) is then refused;
- a goal that also writes the test. §4.1 finds the written occurrence and
  returns, so the call beside it is not specialised. Making the rungs
  cumulative would change motives that are found today, which this round
  does not do.

## 5. Mechanism B: rebuilding the value around `z`

`field_rewrap` reads a scrutinee as a constructor field and says what
abstracting that field does to the value it came from. `fst(snd v)` answers
`(v, ⟨fst v, ⟨z, snd(snd v)⟩⟩)` — the same pair, the same annotations, this
field replaced by `z`, every other component still projected out of `v`. The
abstraction then replaces occurrences of `v`, not of the field.

- For a **single-constructor** inductive the arm's value is the scrutinee term
  itself, so the goal mentions `v` directly.
- For a **multi-constructor** one it is the case binder `x` under an injection,
  and the goal mentions `inl(x)`; abstracting `x` rewrites inside the injection,
  which is the same answer.

The obligation here is `rep[field/z] ≡ v` — Σ-η plus `Unit`-η, i.e. surjective
pairing, which the kernel has and which the hand-written motives at these
fourteen sites were already relying on. That is why this rung produces a term
to be *checked* rather than a proof of anything: the identity it rests on is
the kernel's, and the kernel is asked.

`None` for anything that is not a `fst` off a chain of `snd`s, which is every
scrutinee §4.1 already handles.

## 6. How it composes with the equation binding

`match h : e { … }` (`docs/match-equation-split-design.md`) is a motive
*decoration*: `elab_convoy` wraps whatever motive it is handed in
`λ z => (e = z) -> M z` and applies the result to `refl`. It takes the motive
as an opaque `Type` over one binder, exactly as every other consumer does, so
the two features compose without either knowing about the other — and the
composition is now worth something, because before this round the convoy's
"what does this arm know" was routinely paired with a hand-written "what is this
arm proving". `std/list`'s `filter_filter` is the demonstration: it keeps its
`match e : p(h)` and its `j`, and loses its nine-line motive.

## 7. What this does not do

- **It does not guess.** Nothing is abstracted that is not the scrutinee, up to
  conversion, at a position the goal is stuck on. The sibling-field control in
  `crates/elab/tests/motive_synth.rs` pins the case where over-abstraction would
  be tempting and wrong.
- **It does not rescue an inference-position `match`.** A split whose result is
  *applied* — `match m as λ y => … { … }(p)`, the convoy-by-application idiom the
  order kits use — has no expected type to abstract, and still writes its motive.
  One of the fourteen `Int` sites turned out to be this shape (§8).
- **It does not touch `generalize_index`** (`indexed.rs` §6.1), which is the
  same `Var`-only move for an indexed family's index. No customer asked; when
  one does, it is this operation with the same three rungs.

## 8. What it collected

Twenty-three written motives deleted from the library, all verified by the
kernel:

- `lib/std/data/list.hthr` — `len_filter`, `filter_append`, `filter_filter`,
  `filter_map`, `mem_filter` (5).
- `lib/lang/list_algos.hthr` — `le_head_insert`, `insert_sorted`, `count_insert`,
  `len_insert`, `mem_insert` (5). These split on a *decision*, so their goals
  reduce through `or_pick` rather than through `filter`; same rung.
- `lib/std/num/int.hthr` — `neg_neg`, `isucc_ipred`, `ipred_isucc`, `neg_isucc` ×2,
  `neg_ipred`, `add_isucc`, `add_ipred`, `add_neg`, `mul_neg_r` ×2, `mul_isucc`,
  `lt_irrefl` (13 of the issue's 14).

The fourteenth, `le_of_lt`'s inner split on `m`, is **not** this defect: it is
applied to its hypothesis, so it is an inference position convoying `p` past the
split — the shape the twelve order-kit motives have, which the issue already
excluded. Its motive stays, with a comment saying which issue owns it.
