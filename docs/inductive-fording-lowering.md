# Indexed families, route 2b: lowering by fording over an irrelevant `sEq`

Status: **scheme, written before any code** — this is the design round for
the general (fording) case of `issues/indexed-families.md`, route 2b, whose
*acceptance* prototype landed 2026-07-29
(`crates/elab/tests/indexed_route_2b.rs`, 9 tests) and whose generator this
document specifies. The order of work is the tiers'
(`docs/inductive-tier1-wf-lowering.md`, `docs/inductive-indexed-lowering.md`
are the precedents): this document → a hand prototype against the real
kernel for the corners the 2b acceptance did not reach (§13.1) → the
generator (§13.2). The hazard class is the tiers': a lowering bug does not
produce a rejection, it produces a **checked theorem about a type the user
did not write**, and review of this document is what catches it.

This document is a **sibling of `docs/inductive-indexed-lowering.md`**, not a
replacement. That document owns the fragment where the family is defined by
recursion *on the index* (constructor-headed result indices, recursive
fields at pattern variables); this one owns its complement, which that
document's §8.1 currently rejects with messages naming this route. §3 states
exactly where the boundary moves and what stays rejected.

Conventions are tier 0's (`docs/inductive-tier0-lowering.md`): `⟦T⟧` for the
lowering of a surface type, `⌜T⌝` for a code with `El ⌜T⌝ ≡ T`, kernel names
from `crates/kernel/src/term.rs`, `Γ` the ambient context. `I` is the index
type and `li` its level; `l` is the skeleton's level; `l''` a motive's.
Everything about `sEq`/`srefl`/`transp` is `docs/sprop-design.md` (§2–§5),
and the strip's head-only limit is `docs/metatheory-ch07-extensions.md`
§22 — both are cited, never restated.

---

## 1. What this covers, in one sentence

A declaration whose type is a family over an index and whose result indices
are **computed** — `App(n, m, f: Term(n), a: Term(m)) : Term(plus(n, m))`,
`Node(…) : Tree(Succ(plus(n, m)))`, `Even(…) : Ev(Succ(Succ(n)))` — lowers
to a **skeleton** (the same declaration with its indices erased, lowered by
the *unindexed* tiers verbatim), a **measure** `μ : Skel → I` computed by the
skeleton's own eliminator, and the forded family

```
⟦D<ā>(m)⟧  =  Σ^{l,li}(s : ⟦Skel<ā>⟧). sEq^{li}(I; μ s; m)
```

with the index equation living at `sEq`, where the kernel's irrelevance arm
erases it. Values are the visible data, value equality costs no transport
lemmas, and `match` β is definitional exactly at those constructors that
would have been route-1-eligible on their own (§8.4 — the prototype's
finding, generalized and made a rule).

## 2. Surface form

**The grammar does not change.** `parse_result_index`
(`crates/elab/src/inductive.rs:1811`) already receives the result annotation
as an arbitrary `Expr`; today it rejects everything that is not a depth-one
linear pattern. This round moves that rejection line, and touches
`crates/syntax` not at all.

```
inductive Term : (n: Nat) -> Type {
    Lit                                          : Term(Succ(0)),
    App(n: Nat, m: Nat, f: Term(n), a: Term(m))  : Term(plus(n, m)),
}
```

Field roles, which §3 turns into a predicate and §4–§8 consume:

- a **child** is a field whose type is a recursive occurrence `D<ā>(x)`;
- a **child-index field** is a field named as the index of exactly one
  child (`n` and `m` above). It is **not stored** (§4.2) — the same
  "pattern-variable fields are index, not payload" decision as
  `docs/inductive-indexed-lowering.md` §4.1, reached here by a different
  argument (§5);
- every other field is **payload**, stored in the skeleton, and may be of
  index type (`Rep(n: Nat, x: A) : Vec<A>(n)` — `n` indexes no child, so it
  is payload and `μ` reads it back).

The constructor's **result index** `e_c` may be any expression at type `I`
over the constructor's child-index and payload fields. That is the whole
widening: route 1 constrains `e_c` to a pattern, route 2b does not constrain
it at all.

A `record` still cannot be indexed, for the reason route 1 gives (one
constructor, nothing to vary).

## 3. Classification

The classifier stays a **total function over declarations**, and this round
adds one destination. Read in order; every arm names where the declaration
goes.

```
has an index telescope?
├── no  ────────────────────────────► tier 0 / tier 1 (unchanged)
└── yes
    ├── every ctor route-1-eligible ─► route 1 (indexed.rs, unchanged)
    ├── every ctor 2b-eligible ──────► route 2b (this document)
    └── otherwise ───────────────────► rejected, §3.3, naming the ctor
```

Routing is **per declaration, not per constructor**: route 3 (fording one
branch of a route-1 family) was expected to fail on 2026-07-28 and does —
the recursion's code exists only at the predecessor index and an `Id` does
not relocate it, which is `docs/branching-inductives-choice.md` §10's
rejected code-tables encoding wearing a different hat. A declaration with
one non-route-1 constructor fords **whole**.

### 3.1 Route-1 eligibility (restated, unchanged)

`docs/inductive-indexed-lowering.md` §3: every constructor's result index is
a depth-one linear constructor-headed pattern over its own fields, every
child sits at a pattern variable that is a *recursive* argument of the index
constructor, every field type has a code. Unchanged by this round —
a declaration that qualifies keeps lowering by recursion on the index, which
is strictly better (no stored equation, no measure, no cast anywhere).

### 3.2 Route-2b eligibility

A constructor `c` is **2b-eligible** when all of:

- **(F1) Child indices are variables.** Every child's written index is a
  bare variable naming a field of `c` at type `I`.
- **(F2) Child indices are linear.** No two children name the same
  child-index field.
- **(F3) No payload depends on a child index.** No stored field's type
  mentions a child-index field.
- **(F4) The result index elaborates.** `e_c` is any expression at type `I`
  over `c`'s child-index and payload fields.
- **(F5) Every field type has a code** — tier 1's restriction, unchanged.

and the declaration is 2b-eligible when every constructor is. Note what is
**absent**: any condition on the *shape* of `e_c`, any bound on branching,
any bound on pattern depth.

Why F1–F3 are the conditions, and not fewer, is §5 and §10; each has its own
diagnostic in §3.3.

### 3.3 What still rejects, with its message

Every one of these is a message the generator owes; the first three are new,
the rest are today's text with its destination corrected.

| case | example | message |
|---|---|---|
| **uniform bare-variable index** | every ctor `: D(n)` | unchanged (2026-08-01): "a **parameter**, not an index" + `record D(n: Nat)` |
| **child at a non-variable index** (F1) | `Node(l: T(0), r: T(n)) : T(Succ(n))` | "`l`'s index `0` is not a variable: fording recomputes a child's index from the child, so a constructor may only pin it by *naming* it. Constraining it needs the coherence predicate of `docs/acc-via-w.md` (§10.3 here), which is not generated." |
| **two children at one index** (F2) | `Node(n, l: T(n), r: T(n)) : T(plus(n,n))` | "`l` and `r` share the index variable `n`; the skeleton cannot record that they agree — a label cannot mention its children (`docs/inductive-tier1-wf-lowering.md` §2) — so the constraint would need the coherence predicate (§10.3). Give the children separate indices, or state the family so it is route-1-eligible." |
| **payload depends on a child index** (F3) | `Cons(n, x: Fin(n), xs: Vec(n))` | "`x`'s type mentions `n`, which fords away: `n` is recomputed from `xs`, and a child is not in scope in a payload field's type (`…tier1-wf-lowering.md` §2). This declaration *is* route-1-eligible if every result index is a pattern — see docs/inductive-indexed-lowering.md §3." |
| **field without a code** (F5) | — | tier 1's message, unchanged |
| **mixed** | one ctor fails F1–F3, another fails route 1 | reject naming **both** constructors and both reasons — the declaration is in neither fragment, and saying only one is what sends a user in a circle |
| **multi-index** | `: (n: Nat) -> (m: Nat) -> Type` | unchanged (§8.4 of route 1's doc) |
| **index type restrictions** | parameterized/indexed/container index type | unchanged (`index_type`, `inductive.rs:686`) |

Note one restriction that survives *without* its reason: an index type must
have **at least two constructors**. That rule is load-bearing for route 1
(a one-constructor index emits no `Case` node, so §10.1's fingerprint has
nothing to key on); for 2b the fingerprint reads the nominal tag out of the
**skeleton** (§6.3), where `tag_of` already looks, so the reason is gone.
Kept anyway this round, so there is one classifier and not two; recorded
here as the place to relax it if something wants a `Unit`-indexed family.

### 3.4 One worked example per class

- **Route 1, unchanged**: `Vec`, `Fin`, `Bal` — the result index is a
  pattern, children at pattern variables.
- **Computed result index** (the motivating class): `App(n, m, f: Term(n),
  a: Term(m)) : Term(plus(n, m))`. F1–F5 hold; `μ(app f a) = plus(μ f, μ a)`.
- **Deep pattern**: `ESS(n, p: Ev(n)) : Ev(Succ(Succ(n)))`. Route 1 rejects
  it as "deeper than one constructor"; 2b generates it with no special case
  at all — `μ(ess p) = S (S (μ p))` — and its `match` β is
  form-B (§8.3), because the outer `Succ`'s argument is not a variable.
- **Branching with a computed index** (the Wf-skeleton case, §10):
  `Node(n, m, l: Tree(n), r: Tree(m)) : Tree(Succ(plus(n, m)))`.
- **Non-uniform bare variable**: `Any(n) : D(n)` alongside `Z : D(0)` —
  2b-eligible, `μ(any) = n` reading the stored payload `n`.
- **Rejected**: `Node(n, l: T(n), r: T(n)) : T(plus(n,n))` (F2).

## 4. The skeleton

### 4.1 Which tier lowers it, and by what test

> **The skeleton is the declaration with every index erased, lowered by the
> unindexed tiers, unchanged.**

Erasure: a child's type `D<ā>(x)` becomes `D_s<ā>`, the result annotations
are dropped, and the child-index fields are deleted (§4.2). What remains is
an ordinary declaration, and it takes the ordinary shape test —
`Inductive::recursive`: some constructor has a child ⇒ `Wf^l(x : S). n`
(`wf.rs`, `docs/inductive-tier1-wf-lowering.md`); no constructor has one ⇒
tier 0's sum-of-Σs.

This is the single most consequential sentence in the document, and it
corrects a reading the 2b acceptance prototype invites. That prototype's
skeleton is `docs/inductive-tier1-lowering.md`'s exact-height encoding
`Σ(h : Nat). El (spine h)` — a scheme that was **retired as a generator
path** on 2026-07-26 (`…tier1-wf-lowering.md` §9: linear declarations fold
into `Wf`, and the height machinery is used by no lowering). So the
generator's skeleton for any recursive family is a `Wf`, always; "fording
over a `Wf` skeleton" is not an exotic corner of this scheme, it is the
**main line**, and §10 treats it as such.

### 4.2 What is stored, and what the child-index fields become

| surface field | in the skeleton |
|---|---|
| payload | stored, in the label's Σ spine (tier 0 §3.1, verbatim) |
| child | a child in the `Vec` (tier 1 §5), index erased |
| child-index field | **not stored** |

Eliding the child-index field is forced, not chosen. Storing `n` alongside
`xs : Vec(n)` and *not* constraining it makes the family a quotient (a
value at index `S 5` whose tail has three elements — precisely
`docs/testing-generated-terms.md`'s axis 4, and the prototype's
`negative_controls_mismatched_indices_reject` is what would catch it).
Constraining it requires an equation between the stored `n` and `μ(xs)`
inside the skeleton — which cannot be written, because the skeleton's label
cannot mention its own children (tier 1 §2). Eliding it dissolves the
question: `n` **is** `μ(xs)`, definitionally, and the constructor's surface
argument for `n` is erased in the term exactly as route 1 erases a pattern
variable.

F3 is the direct cost of that decision, and the reason it is a condition and
not a repair.

## 5. The index measure `μ`

```
μ : ⟦Skel<ā>⟧ → I

μ  =  elim_Wf^{li}( _. I
                  ; a cs ih. Case-on-tag(a) {
                        c_i ↦ ⟦e_i⟧[ x_t ↦ ih ι_t ,  p_j ↦ fst (snd^{j+1} a) ]
                    } cs ih )
```

— and, at a non-recursive skeleton, the same branch bodies under tier 0's
`const_case_tree` at motive `I`, with no `ih`.

Three things to read off that display:

1. **`μ` is the constructor's own written result index**, with each
   child-index variable replaced by the recursion at that child and each
   payload variable by its projection out of the label. Nothing about `e_c`
   is inspected, which is why §3.2 has no condition on its shape.
2. **It is `wf.rs`'s recursor device at a new motive.** The `cs`/`ih`
   threading through the `Case` motive (`…tier1-wf-lowering.md` §6.2) is
   needed for the same reason as always — outside a tag branch the arity
   `n[a/x]` is stuck on a variable, so neither `Vec` nor `Fin` reduces —
   and it exists once, in `build_elim_wf` behind `Branches::Custom`
   (`crates/elab/src/wf.rs:97`), which route 1's declared-index family
   already reuses. `μ` is its third client and needs no new machinery.
3. **`μ` computes on open data.** `μ (c(b̄))` β-reduces through `elim_Wf`'s
   β at a `sup_f`, then `Case` β at the injection, then `nth`/`ih` at
   literal `Fin` indices — every step is the tier-1 reduction that
   `beta_fires_on_open_children` already pins, with the children left open.
   Everything downstream leans on this.

F1/F2 are exactly what makes `μ` *faithful*: a value's index is recomputed
from its shape, so there is no stored index to disagree with the data. Where
F1 or F2 fails, `μ` still exists but stops being faithful — §10.3.

## 6. The forded type

```
⟦D<ā>(m)⟧  =  Σ^{l,li}( s : ⟦Skel<ā>⟧ ). sEq^{li}(I; μ s; m)      at level l ⊔ li
```

### 6.1 Why the equation sits where it does

Not inside the constructor's payload — it cannot be (§4.2, and the label
cannot mention children) — and not as a coherence predicate over the whole
skeleton (§10.3) — it need not be, given F1/F2. One `sEq` at the top,
relating the recomputed index to the written one, is the whole fording
layer. That is the shape the acceptance prototype validated, and the results
it earned carry over verbatim (`issues/indexed-families.md` 2026-07-29):
proof-swapped values are convertible outright, the cross-spelling transport
lemma is `refl`, and mismatched indices genuinely reject.

### 6.2 Levels and codes

The Σ is at `l ⊔ li` and both components have codes (`TmSigma`, `TmSEq` —
`docs/sprop-design.md` §6), so **a forded family may be a field of another
declaration**, which route 1's families can also do and tier-2 encodings
could not. `li` is `0` at `Nat` and the index declaration's level otherwise;
uniformly-level-0 suites cannot see a dropped join, so §13's checklist
carries a nonzero-level case (route 1's §10.5 lesson, not re-learned).

### 6.3 Reading the form back

The consumers (`build_ctor`, `match`, the type-position bridge in
`elab_check`) need a `forded_of` in the shape of `indexed_of`
(`indexed.rs:300`): a `Type::Sigma` whose `snd` is a `Type::SEq` whose `lhs`
is the `μ` node applied at the Σ binder. Three parts come back: the
skeleton type, `μ` (as a node with a placeholder in its scrutinee slot —
kept *whole*, never branch-by-branch, for the reason route 1 records at
`IndexedFam::at`), and the index `m`.

This fingerprint is **cheaper and more robust than route 1's** (§14.1): the
declaration's identity is read by `tag_of` out of the skeleton, where it
already lives and where a `Wf` is already seen through (tier 1 §4). A user
cannot forge the shape, because `sEq` is generator-internal by policy
(`docs/sprop-design.md` §1) and unwritable at the surface.

## 7. Constructors

```
⟦c(b̄)⟧  =  ⟨ skel_c( stored b̄ ; fst v_1 … fst v_k ) ,  π_c ⟩
```

— the skeleton constructor (tier 0 §4 / tier 1 §5, called with the stored
arguments and the *skeletons* of the forded children), paired with the index
proof. With `ŝ` the skeleton just built and `x_t` the child-index argument
written for child `t`:

```
π_c  =  transp^{li,li}( I ; z. sEq(I; μ ŝ; e_c[x_1 ↦ z, …]) ; μ (fst v_1) ; ⟦x_1⟧ ; snd v_1
        ⋯ transp( … child k … ;
             srefl^{li}(I; μ ŝ) ) )
```

Read inside out: `μ ŝ ≡ e_c[x_t ↦ μ (fst v_t)]` by `μ`'s β (§5 fact 3), so
`srefl` types at the innermost motive instance; each child's stored proof
`snd v_t : sEq(I; μ (fst v_t); ⟦x_t⟧)` then rewrites one child's measure to
the index the user wrote. The written index `e_c[x̄]` is checked against the
expected family's index by **one conversion**, exactly as route 1 does
(`build_indexed_ctor`, `indexed.rs:830`), and the diagnostic follows that
one.

**`π_c` is invisible.** It inhabits `sEq`, so the irrelevance arm accepts it
against any other proof without inspecting either
(`docs/sprop-design.md` §5.2). Two consequences worth stating, because both
save work: the generator may emit the simplest well-typed proof it can (the
chain above) with no concern for its shape; and §9's cast rule does **not**
bind here — a `transp` whose *type* is irrelevant is erased before any strip
question arises.

## 8. The eliminator

One construction, as in every tier document: the derived eliminator, `ih`
unused when the surface `match` has no self-call.

### 8.1 The fording motive

Given a motive `M` over `(Γ, i : I, z : ⟦D<ā>(i)⟧)` at `l''` and a scrutinee
`s : ⟦D<ā>(e)⟧`:

```
Q(σ)  =  Π^{li}(m' : I). Π^{li}(e' : sEq(I; μ σ; m')). M[m', ⟨σ, e'⟩]     over (Γ, σ : Skel)

elim(s)  =  skel_elim( σ. Q(σ) ; arms ; fst s )  ⟦e⟧  (snd s)
```

`skel_elim` is `build_elim_wf` at motive `Q` (or tier 0's `Case` tree, at a
non-recursive skeleton) — the **fourth** client of the same device. The
recursion is on the skeleton; the index and the stored proof are consumed by
the two trailing applications. This is the prototype's `vec_rec`, with `len`
generalized to `μ` and the `List` recursion generalized to the skeleton's.

Inside constructor `c`'s branch, with children `nth(cs'; ι_t)`, ihs
`ihQ_t = ih' ι_t : Q(child_t)`, and `ŝ = sup_f(ι_c(label); cs')` the
rebuilt skeleton, the arm binds:

| surface binder | lowering | type |
|---|---|---|
| payload field `j` | `fst (snd^{j+1} label)` | its declared type |
| child-index field of child `t` | `μ (child_t)` | `I` |
| child `t` | `⟨child_t, srefl(μ child_t)⟩` | `⟦D<ā>(μ child_t)⟧` |
| self-call on child `t` | `ihQ_t (μ child_t) srefl` | `M[μ child_t, ⟨child_t, srefl⟩]` |

and the *proof component of every child is `srefl`* — the fording layer
never reconstructs a child's equation, because the child's index binder is
its own measure. That is F1/F2 paying for itself a second time.

### 8.2 Form A — index inversion (definitional β)

When `e_c = I_k(x̄)` with `x̄` **distinct child-index variables** — i.e.
when `c` would have been route-1-eligible on its own — the arm inverts the
*motive's* index instead of consuming the stored proof:

```
arm_c  =  λ(m' : I). elim_I( ẑ. Π(e' : sEq(I; μ ŝ; ẑ)). M[ẑ, ⟨ŝ, e'⟩]
                           ; branch k   ↦ λe'. ⟦arm body⟧    -- binders at the branch's own arguments
                           ; branch j≠k ↦ λe'. elim_Empty( … ; transp(I; z. El(is_k z); μ ŝ; ẑ_j; e'; ⟨⟩) )
                           ) (m')
```

The `j ≠ k` branches are no-confusion: `μ ŝ` is `I_k`-headed and the branch's
index is `I_j`-headed, so transporting `e'` through the tag predicate
`is_k : I → Ty 0` lands in `Empty`. At `Nat` these are the prototype's
`zero_pred`/`is_succ` and `pred` verbatim; at a declared index they are
`wf.rs` §7.1's tag predicate and §7.2's `child_projection`, which exist but
have never been used for this purpose — §14.4 records that as a seam and
§13 defers it: **form A is generated at a `Nat` index this round; a declared
index takes form B everywhere**, with the β consequence stated to the user
in the doc rather than discovered.

In form A the stored proof is **consulted nowhere**: every equation the arm
produces sits at `sEq` type. That is what makes β definitional on open data,
and it is the prototype's measured result
(`beta_fires_on_open_recursive_data`), here restated as a rule:

> **Inside 2b, a constructor gets definitional open-data β exactly when it
> would have been route-1-eligible on its own.**

Partial inversion buys nothing and is not attempted: at
`e_c = Succ(plus(n,m))` peeling the outer `Succ` still leaves the arm owing
a cast at the inner computed argument, so the β obligation is unchanged and
the term is larger. Form A is all-or-nothing per constructor.

### 8.3 Form B — the transp arm (everything else)

```
arm_c  =  λ(m' : I). λ(e' : sEq(I; μ ŝ; m')).
             transp^{li,li⊔l''}( I ; z. Π(e₀ : sEq(I; μ ŝ; z)). M[z, ⟨ŝ, e₀⟩]
                               ; μ ŝ ; m' ; e'
                               ; λ(e₀ : sEq(I; μ ŝ; μ ŝ)). ⟦arm body⟧ ) e'
```

The `Π`-motive is not decoration: `M[z, ⟨ŝ, ?⟩]` alone is unstateable,
because the pair's second component's type depends on `z` and there is no
canonical proof at an arbitrary `z`. Transporting the *function* and
applying it afterwards is the only shape available, and it is what §8.4's
honest β statement is about.

The arm body is checked at `M[μ ŝ, ⟨ŝ, e₀⟩]`, where `μ ŝ ≡ e_c[x̄ ↦ μ child]`
by β and `⟨ŝ, e₀⟩` converts with the constructor term by Σ-η, `Unit` η on the
rebuilt label (route 1 §8.2 fact 2's obligation, unchanged) and `sEq`
irrelevance on the proofs. No cast appears *inside* the arm.

### 8.4 What β actually does, stated honestly

**Measured 2026-08-03**, `crates/elab/tests/indexed_route_2b_wf.rs` (§13.1
item 2) — the claim was marked owed here because the 2026-07-29 log entry
asserted it from inspection and `indexed_route_2b.rs` contains no
transp-only eliminator. All three bullets below are now assertions in that
file, the second and third in the *same* test so the contrast cannot drift.

- **Form A**: `match (c(…)) { c(…) ⇒ b } ≡ b` with every binder open —
  definitional (`form_a_beta_is_definitional_on_open_recursive_data`, over a
  branching `Wf` skeleton and at an open payload type).
- **Form B, a stored proof that whnfs to `srefl`**: the arm's `transp` fires
  by β (`docs/sprop-design.md` §5.1) and the reduct is the arm body.
  Definitional — and this is **not** the same as "closed data": the measured
  positive holds with the element, the tail *and* the index all open, the
  value's proof being `srefl` at its own measure.
- **Form B, a stored proof that is neutral** — which is what a constructor
  built over an open forded child has, its proof being a `transp` chain over
  a variable: the arm's `transp` does not β, and the residue is a stuck
  `App(transp(…), e')`. The head-only strip does **not** rescue it: the head
  of the compared term is the `App`, not the `transp`
  (`docs/metatheory-ch07-extensions.md` §22.1's measured `elim(cast)` shape,
  in a new position). β is **propositional** there, not strip-guarded.

So the honest key is the *proof*, not the data: form B computes exactly
where the index equation is `srefl`, and a forded constructor manufactures a
non-`srefl` proof as soon as one of its children is open.

That last bullet is sharper than the issue log's "degrades to strip-guarded"
and should replace it. It is also §9's honest limit in the wild: at the
redex, `transp`'s endpoints `μ ŝ` and `m' := ⟦e⟧` **are** convertible (that
is why the value typechecked), so β-reduction *creates* a redundant cast out
of a term that had none — exactly §22.3's "`⌊t⌋ = t` is not preserved by
reduction", now with a generator that meets it. The consequence is bounded
and stated: a spurious `NotConvertible` at check time, never an unsound
accept and never non-termination.

Under the 2026-07-28 currency bar this is **mechanical residue, not setoid
contamination** — the value equality half of the bar is untouched (§11) —
but it is residue the user sees in a *proof*, so the surface must say so:
§12's rejection list is where a user is told which constructors of their own
declaration compute and which do not.

## 9. The cast rule, as a stated obligation

> **The generator never emits a `transp` at convertible endpoints — in
> VALUE, INDEX or CODE position.**

Sources: the 2026-07-29 finding (a redundant cast is opaque to elimination,
pinned as a negative in `index_casts_are_invisible_through_the_strip`) and
the 2026-08-03 scope note off `docs/metatheory-ch07-extensions.md` §22.4
(the same gap has a type-former face — a `transp` inside a `Vec`/`Wf` length
or an `El` argument makes a canonical type read as neutral, and
`docs/sprop-design.md` §5.4's first derived fact overstates this).

Where the generator satisfies it, by construction:

1. **No re-indexing coercion, ever.** A forded value written at one index
   spelling and used at a convertible other one is passed **bare**; the
   `sEq` component converts endpoint-wise, so a cast is unnecessary and
   (being redundant) harmful. This is the rule's main teeth, and it is a
   rule about what the generator must *not* helpfully insert.
2. **§7's `π_c` is exempt** — it lands at `sEq`, where irrelevance erases it
   before any strip question is asked.
3. **§8.3's arm cast is load-bearing at emission**: its endpoints are `μ ŝ`
   and the *bound* `m'`, which do not convert under any instantiation the
   generator can see. §8.4 records what reduction does to it.
4. **Index and code positions are cast-free by construction**: the skeleton's
   `Wf` arity is a `Case` on the label, the family's Σ mentions `μ s`, and
   the index `m` is the user's own term. No emitted `Vec` length, `Wf`
   arity or `El` code contains a `transp` at all.

How a violation is caught — this is the part that must be a *test*, not a
promise: a **structural walker** over every term the 2b generator emits,
asserting that no `Transp` node occurs under a `Type::Vec { len }`,
`Type::Wf { arity }` or `Type::El { tm }`, and that every `Transp` at a
relevant type has endpoints the walker cannot prove convertible by syntactic
equality. Run it on the acceptance suite's emitted terms (§13.2 item 7), and
keep §22.4's two kernel-side negatives (`Vec^l(T; transp(…;e;ze))` against
`Unit^l`, `El^l(transp(…;e;TmNat))` against `Nat`) as the pinning of *why*
— they belong to `issues/seq-strip-type-former-negatives.md` and are cited
here, not duplicated.

## 10. `Wf`-skeleton composition — the untested corner

The issue carries this as "the ONE UNTESTED CORNER of the scheme"
(2026-07-29 caveat). It is treated here head-on, in three parts.

### 10.1 The verdict

**Fording composes with a branching `Wf` skeleton, with no new fording
machinery** — and it must, because §4.1 makes the `Wf` skeleton the *only*
skeleton a recursive family ever gets. The argument:

- the fording layer never inspects the skeleton's recursion. `μ` and `Q` are
  **motives**; whether the recursion carrying them is `elim_Nat`, a `Case`
  tree or `elim_Wf` is `build_elim_wf`'s business, and that dispatch already
  exists and is already exercised at motive `Ty l` by route 1's
  declared-index family (`indexed.rs:563`) — §5 and §8.1 add motives `I` and
  `Q`, not a new recursion scheme;
- the two `Wf`-specific hazards are known and paid elsewhere: the refined
  arity (`cs`/`ih` threaded through the `Case` motive, `…tier1-wf-lowering.md`
  §6.2) and the `Unit`-η identity between a branch-rebuilt `sup_f` and the
  declared constructor (route 1 §8.2 fact 2). Both are the *skeleton's*
  obligations and neither mentions the index;
- branching is free in the same sense route 1 found it free: each child
  contributes `μ(child_t)` to `e_c` independently, and `e_c` may combine
  them by any function (`Succ(plus(n, m))`) because `μ` is a fold, not a
  pattern match. Exact-height fording's §8.1 wall (a stuck `max`) does not
  arise — there is no computed *height*; the measure is the user's index.

**This is the claim the prototype phase must earn** (§13.1 item 1), and it is
the reason the prototype phase exists at all.

### 10.2 The coherence question, answered

`issues/indexed-families.md` (2026-07-27) says fording over `Wf` inherits
`docs/acc-via-w.md`'s coherence predicate — "a per-declaration skeleton,
`idx` by `elim_Wf`, a code-valued `coh` by `elim_Wf`, and an `Id` at the
top". Three of those four appear above; **`coh` does not**, and the reason
is precise:

> A coherence predicate exists to say that a stored index agrees with the
> data. §4.2 stores no index. `μ` recomputes it, F1/F2 make the
> recomputation faithful, and there is nothing left for `coh` to assert.

The `Id` at the top is an `sEq`, which is the whole point of 2b over
route 2, and it is one equation about the *root* index rather than a
predicate over every node.

### 10.3 Where `coh` would come back, and what happens instead

Exactly at F1/F2's failures. If a child sits at a constant or computed index
(`l : T(0)`, `l : T(plus n m)`), or two children share one index variable,
the missing constraint relates a child's measure to something the label
cannot mention, so the only place left for it is a **code-valued
`coh : Skel → Ty l` by `elim_Wf`**, with the family becoming
`Σ(s). Σ(_ : El (coh s)). sEq(I; μ s; m)` — `acc-via-w.md`'s predicate,
re-derived. That is a scheme round of its own (the `coh` recursion, its
interaction with `μ`, whether `match` β survives it), and this round
**rejects instead**, with §3.3's two diagnostics naming the predicate as the
extension. Recording the restriction rather than half-implementing it is the
`Wf`-round discipline (`docs/wf-former-design.md` §1.2's shed-weight rule).

## 11. Value equality, no-confusion, and the setoid bar

Inherited from the acceptance prototype, restated so the generator knows
what it may rely on:

- **Value equality is equality of the visible data.** Two forded values with
  the same skeleton are convertible whatever their proofs
  (`value_equality_needs_no_transport_lemmas`), and the route-2 contrast
  (`Id`-stored proofs obstructing exactly this) stays pinned as the reason
  the round chose `sEq`.
- **The cross-spelling transport lemma is `refl`.** A value used at two
  convertible index spellings maps to the same thing definitionally — hence
  §9's rule 1.
- **Index injectivity is not a lemma**, as in route 1: it is the typing. But
  the *converse* is new and worth saying: from `⟨s, e⟩ : D(m)` a user learns
  `μ s ≡ m` **only up to `sEq`**, which is irrelevant and therefore carries
  no computational content. A user who needs `Id(I; μ s; m)` cannot get it
  from the family; that is the standing price of irrelevance and is not a
  defect to fix here.
- **Disjointness and field injectivity** are the *skeleton's*, verbatim
  (tier 0 §6, tier 1 §7): the equation component contributes nothing to
  either, being irrelevant. Cross-index disjointness is *not* vacuous the
  way route 1's is (there is no per-index branch to be ill-formed), so an
  `absurd` between constructors at different indices goes through the
  skeleton's tag predicate — the same term route 1 would have needed.
  Nothing is generated for it this round (§12).

## 12. Surface `match`, guards, and what is not supported

### 12.1 `match`

`match s { … }` on `s : D<ā>(e)` elaborates to §8's eliminator. The motive
rule is route 1's §6.1 **unchanged**: a *variable* index is generalized (its
occurrences in the goal become the motive's index binder); anything else
requires the goal not to need per-arm refinement, or an explicit two-binder
motive `as λ n z => T`. No new inference.

Arm binders are §8.1's table. A binder for a child-index field is legal and
receives `μ(child)` — the analogue of route 1's "the pattern variable *is*
the eliminator's binder", one indirection longer.

### 12.2 Self-calls

`GuardKind::Wf` applies as it stands: children are the forded child terms
`⟨child_t, srefl⟩`, the ih is `ihQ_t (μ child_t) srefl`, and matching is on
the *term* (tier 1 §6.4). `Guard.rebind` carries **one index term per
descendant**, in the shape route 1 reshaped it into on 2026-08-03 — the
index term being `μ(child_t)` rather than a pattern variable. That is the
whole change: the guard's rule "every other argument unchanged, the index
argument re-fixed by the ih" is stated over terms already, so a computed
index needs no relaxation, only the right term.

### 12.3 Not supported this round, each with its message

- **`absurd`/`inj` surface forms on a forded family**: "no-confusion on a
  forded family is not generated; the skeleton's own `absurd`/`inj` are
  (docs/inductive-fording-lowering.md §11)." Same status as route 1 §7 —
  nothing has needed them.
- **Multi-index**: route 1 §8.4's message, unchanged.
- **A forded family as a written type argument** (`f<Term(3)>`): route 1's
  gap, inherited verbatim.
- **`coh`-requiring declarations**: §3.3's two F1/F2 messages.
- **Form A at a declared index**: not a rejection — a *β* limitation, so it
  is documented (§8.2) rather than diagnosed. A declaration is never
  rejected for it.

## 13. Acceptance checklist

Hand prototype first, as kernel terms against the real kernel, then the
generator — the tier discipline, and the reason
`crates/elab/tests/indexed_route_2b.rs` exists at all. Every item follows
`docs/testing-generated-terms.md`'s axes: literal **and** neutral scrutinee,
an **open** element type, a **checking** position, and a negative control per
encoding decision.

### 13.1 Prototype (new file, beside the 2b acceptance)

**Landed 2026-08-03**: `crates/elab/tests/indexed_route_2b_wf.rs`, 11 tests,
all seven items below. One deviation from the list as written: items 1–5 and
7 are carried by a **single** declaration rather than a separate `Tree` —
`Rope { Nil : R(0), Cons(n, x, xs: R(n)) : R(S n), Cat(n, m, l: R(n),
r: R(m)) : R(plus(n, m)) }` — because one vehicle with both an invertible
and a computed constructor is what makes §8.2's per-constructor claim
falsifiable at all (the two forms are compared on the same scrutinee, in the
same eliminator). Three de Bruijn defects were found and fixed in the
building, all of them annotation-scoping and all invisible at a closed
payload type or a constant motive — the axes earning their keep again: a
`Case`'s summand types are scoped at the `Case`, an application's `cod`
mentions its *bound* variable (not the literal it is applied at), and a
`cod` that ignores its binder still has to be shifted past it.

1. **The `Wf` skeleton, forded** (§10.1 — the corner the round exists to
   close). `Tree` with `Leaf : Tree(0)` and
   `Node(n, m, l: Tree(n), r: Tree(m)) : Tree(Succ(plus(n,m)))`, over an
   **open element code**: skeleton as a `Wf`, `μ` by `elim_Wf`, the Σ+`sEq`
   family, both constructors, and the eliminator. Literal scrutinee that
   **computes** (`conv` against the reduct, not just `check`), neutral
   scrutinee typed, and a checking position (a `refl`-proved theorem about
   `μ`).
2. **The transp-only eliminator, measured** (§8.4 — today's unmeasured
   claim). Build form B for a computed index and record, as assertions:
   closed β fires; open-recursive-data β **does not**; and the failure is a
   stuck `App(transp …)` rather than an unsound accept. A negative test
   documenting a gap is worth more than a comment claiming there is none.
3. **Form A inside a forded declaration** (§8.2): the same `Tree`'s `Leaf`,
   and a `Vec`-shaped constructor in a declaration that fords for another
   constructor's sake — β definitional on open data through the inversion,
   with the no-confusion branches exercised.
4. **Axis 4, the quotient control**: a skeleton whose measure differs from
   the index does not inhabit the family, whatever proof is tried; two
   values with the same index and different data are inconvertible. This is
   what would catch a dropped `sEq` component or an unfaithful `μ`.
5. **Value equality** (§11): proof-swapped values convertible; the
   cross-spelling lemma checks as `refl`; the route-2 `Id` contrast stays
   pinned in the old file and is cited, not copied.
6. **F1/F2 falsifiers**: hand-build the `coh`-free encoding for a shared
   child index and show it admits a bad value — the evidence behind §3.3's
   rejections, so they are measured restrictions rather than caution.
7. **A nonzero-level case**: a `Type`-valued payload field (family at
   level 1, motive at 0), so a dropped join in `Q`'s Π or the skeleton
   eliminator's level cannot hide (§6.2, route 1 §10.5).

### 13.2 Generator

8. Classifier: every §3.3 row fires with its message; every §3.4 example
   routes where §3 says, including the mixed-rejection row.
9. `Term`/`App`-shaped declaration end to end: declare, construct at open
   indices, `match` with a self-call, a recursive `theorem` over it.
10. The branching forded `Tree` end to end, including a `theorem` by
    induction whose step is at a form-A constructor (so the proof closes) and
    a documented one at a form-B constructor (so §8.4's residue is visible in
    a test rather than in a bug report).
11. Deep pattern (`Ev`) declares and computes — the route-1 rejection that
    becomes generatable.
12. Non-uniform bare-variable index (`Any(n) : D(n)` beside `Z : D(0)`)
    declares; the *uniform* case still rejects with the parameter message.
13. A forded family as a **field of another declaration** (§6.2) and as a
    `fn` result type.
14. §9's structural walker over every emitted term, plus one nonzero-level
    generator test (§13.1 item 7's instance, end to end).

## 14. Known seams, recorded before they bite

1. **`forded_of` is a structural fingerprint**, like `indexed_of` before it
   (route 1 §10.1) — smaller and tag-anchored (§6.3), but still a shape
   match. Any pass that normalizes or restructures emitted terms (a kernel
   `def`, level canonicalization, hash-consing) breaks it, and the symptom
   is "not a forded family" far from the cause.
2. **`μ` is inlined at every occurrence.** The family type contains a whole
   `elim_Wf`, and the eliminator instantiates it several times per arm; a
   forded type appearing in another type multiplies that. Route 1 §10.3's
   note, amplified once more, with the same eventual fix (a kernel `def`)
   and the same place for "acceptable" to get a number
   ([[frontend-benchmarks]]).
3. **Pre-reduced family types are diagnosed, not handled** — route 1 §10.2's
   seam, inherited: a Σ that arrived whnf'd has lost nothing structurally
   (Σ is a whnf), so this is *better* here than at route 1, but a `μ` that
   arrived reduced at a literal index is unrecognizable and takes the same
   re-synthesis fix if something hits it.
4. **Form A at a declared index is unbuilt.** The pieces exist (`wf.rs`
   §7.1's tag predicate, §7.2's `child_projection`) and have never been
   composed into an inversion. Whichever round wants open-data β at a
   declared-index forded family builds it here, and §8.2 is the shape.
5. **β-reduction manufactures redundant casts** (§8.4). The generator emits
   `⌊·⌋`-fixed terms; reduction does not preserve that, and the head-only
   strip cannot see the result under an `App`. Bounded to spurious
   `NotConvertible`s by §22.3, but it is the seam most likely to surface as
   a confusing user-facing error, and the error message for a stuck
   conversion at a forded family should say so.
6. **Two skeletons, one declaration.** The elaborator will hold a synthesized
   skeleton `Inductive` alongside the declared one; they must not drift.
   Building the skeleton **from** the declaration at declaration time (index
   fields deleted, child types erased) and never editing it afterwards is
   what keeps that true — the same discipline as "the shape is tier 0's
   lowering with the recursive fields deleted" (tier 1 §2).

## 15. What this document amends elsewhere

Flagged rather than silently designed around, per the round's rules.

1. **`issues/indexed-families.md`, 2026-07-29 finding (1)** says that at a
   non-invertible index "the transp-only eliminator still types and equality
   stays lemma-free, but open-data β degrades to strip-guarded". Settled by
   measurement 2026-08-03 (§8.4, `indexed_route_2b_wf.rs`): the first two
   clauses **hold**, and the third is wrong twice over. It is not
   strip-guarded — the residue is a stuck `App(transp …)` the head-only
   strip never reaches — and "open data" is the wrong key: form B computes
   on open data whenever the stored proof is `srefl`, and stalls on closed
   data if it is not. The log entry should be amended to the §8.4 wording.
2. **The 2026-07-29 caveat's framing** ("the skeleton here is tier 1; the
   `Wf`-skeleton composition is the one untested corner") understates the
   exposure: since `…tier1-wf-lowering.md` §9 retired exact-height fording as
   a generator path, the `Wf` skeleton is not a corner but the only case the
   generator will ever emit for a recursive family (§4.1). The scheme is
   unaffected; the *risk ranking* is not.
3. **`docs/sprop-design.md` §5.4** already carries the 2026-08-03 correction
   for `Vec`/`Fin`/`El`; §9 here consumes it as a rule and adds nothing, but
   the pinning tests it owes (`issues/seq-strip-type-former-negatives.md`)
   are a dependency of §13.2 item 14 rather than an unrelated errand.
4. **`docs/inductive-indexed-lowering.md` §8.1** should, when this generator
   lands, stop saying "not yet generated" for the computed-index and
   deep-pattern rows and point here instead; the F1/F2/F3 rows are new text
   that document does not have.
