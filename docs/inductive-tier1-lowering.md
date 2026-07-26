# Tier-1 inductive lowering: exact-height fording

Status: **not the generator's scheme.** Superseded 2026-07-26 by
`docs/inductive-tier1-wf-lowering.md`, which lowers *all* of tier 1 —
`List` and `Bits` included — onto the `Wf` former. This document stays as the
costed record of a scheme that was designed, prototyped and not taken, and
its §8 is why: the branching defect it diagnoses is exactly what the former
set was changed to remove (`docs/branching-inductives-choice.md` §15). Its
prototype `crates/elab/tests/tier1_fording.rs` stays **live** as a kernel
stress suite, and its `vec` formula survives as `Type::Vec`'s reduction
semantics.

Original status: scheme written and **validated by hand prototype**,
2026-07-24 —
`crates/elab/tests/tier1_fording.rs` builds every construction below as
kernel terms and checks them with the real kernel (`List<Nat>` for §3–§6,
`Bits` for the multi-constructor parts). The generator is **not** written
yet; per the tier's discipline the scheme comes first, and the prototype
comes before the generator (`issues/inductive-compiler.md`,
`issues/stress-proof-suite.md` item 2). §8 records what this scheme does
*not* cover — branching constructors — and why that is a decision rather
than a coding task.

Tier 1 is the recursive finitary tier: `List`, `Bits`, snoc lists, syntax
trees with a single recursive child. Its hazard class is tier 0's, amplified:
a bug produces a checked proof about the wrong type. Same rule therefore —
this document is the mechanism, and review of it is what catches the bug the
kernel cannot.

Conventions are tier 0's (`docs/inductive-tier0-lowering.md`): `⟦T⟧` for the
lowering of a surface type, `⌜T⌝` for a code with `El ⌜T⌝ ≡ T`, kernel
constructor names from `crates/kernel/src/term.rs`, `Γ` the ambient local
context. Everything in tier 0 §2 (declaration form, parameters
monomorphized, positivity, type-argument inference) carries over unchanged,
and so does the nominal tag of tier 0 §3.3: it is field 0 of every
constructor's field spine here too, and is elided in this document's
displays exactly as it is there.

---

## 1. The dragon, and why the fix is "exact"

The kernel has no recursive types other than `Nat` and `W`. Tier 1 therefore
recurses *on a `Nat`* — "Nat-fording": pick a numeric measure, define the
family of values at each measure by `elim_Nat`, and take the type to be the
Σ over the measure.

The naive version bounds the measure:

```
D_le 0       = ⟦non-recursive constructors⟧
D_le (h+1)   = ⟦all constructors, recursive fields at D_le h⟧
⟦D⟧          = Σ(h : Nat). El (D_le h)          -- WRONG
```

This is the trap named in the issue. `nil` at bound 0 is `⟨⟩`; `nil` at
bound 5 is `inl ⟨⟩` in a five-times-larger type — *different pairs of the
same Σ type*. Definitional equality is then finer than the intended equality
of `List`, every function has to be proved to respect padding, and
`issues/setoid-auto-lifting.md` gets dragged in years early to fix a problem
we created.

The fix is to make the measure **exact**, so that the value determines it:

```
D_ex h   = the values of D of height exactly h
⟦D⟧      = Σ(h : Nat). El (D_ex h)
```

Now `fst` of a value *is* its height, the payload's shape at that height
forces exactly an `h`-deep constructor chain, and the encoding is in
bijection with the intended type — definitionally, with no quotient and no
propositional side conditions. Constructors compute their own height
(`length` for `List`, `1 + child` in general here), which is why this is
available at all: in the finitary tier the height is a computable function of
the value.

Two properties of the result are worth stating up front, because they are
what the prototype pins:

- **Canonical forms are unique.** Two encoded values are convertible iff they
  are the same value; there is no padding degree of freedom
  (`canonical_forms_are_unique`, `bits_type_constructors_and_computation`).
- **β fires on open subterms.** `append (cons a l) ys ≡ cons a (append l ys)`
  with `a`, `l`, `ys` all variables. This is not automatic — see §3 — and it
  is the property that fails for branching constructors (§8).

No `Id` appears anywhere in the encoding: it is built from `Nat`, `Σ`, `+`,
`Unit` and `El` only, all of which either have η (`Σ`, `Unit`) or are
positive with a β rule (`+`, `Nat`). Fording *indices* would reintroduce
`Id`, which has no η; that is the reason indexed families are held back to
their own round (§8.4).

---

## 2. Classification, and what the kernel provides

Tier 1 admits a declaration when every constructor has **at most one
recursive field**, and that field's type is `D` at the declaration's own
parameters. Write

- **base constructors** — no recursive field (`nil`, `Bits::Nil`);
- **step constructors** — exactly one (`cons`, `B0`, `B1`).

Two or more recursive fields in one constructor is the branching case: not
covered, §8. A recursive occurrence *nested inside another type constructor*
(`Rose { Node(List<Rose>) }`) is mutual recursion between two tier-1
declarations, also §8. `D` under a `Π` or in an index is tier 2, as before.

Everything needed is already in the kernel; beyond tier 0's table:

| Need | Kernel |
|---|---|
| the recursion | `Term::ElimNat` with `motive : Type` at the *type* level |
| a family of types | motive `Type::Ty(l)`, so the recursion returns **codes** |
| decoding | `Type::El {level, tm}` |
| the payload family | `Type::Pi` inside the `elim_Nat` motive (§4) |

Two facts the scheme leans on, each exercised in the prototype rather than
assumed:

1. **`elim_Nat` does large elimination.** Its motive is an arbitrary `Type`
   checked at the elimination's level, so `motive := Ty l @ 1 + l` is
   well-formed (`typing.rs:803`), and `El` of the result decodes it
   (`reduce.rs:93`). This is what makes a *type family by recursion on a Nat*
   expressible at all.
2. **Codes compose without a round trip.** In the step, the recursion
   variable *is* a code, so the recursive occurrence is spliced into a
   `TmSigma`/`TmSum` code directly — no `⌜El rec⌝` and no coherence
   obligation.

The consequence to keep in mind is a genuine restriction: **every field type
must have a code.** `Nat`, `Unit`, `Empty`, `Σ`, `+`, `Π`, `Id`, `W`, `Ty l`
all do, so every type the surface can write today does; a field type that is
only a `Type` and not `El` of something would have to be lowered
differently. Tier 0 has no such restriction (it never recurses).

---

## 3. The type and the constructors

### 3.1 The height family

Let the base constructors be `b_1 … b_p` and the step constructors
`s_1 … s_q`, and let `⟦c⟧(X)` be tier 0 §3's field spine for `c` with the
recursive field's type replaced by `X` — tag first, then the fields, `Unit`
terminated. Let `Sum_i T_i` be tier 0 §3.2's right-nested sum spine. Then

```
D_ex : Nat → Ty l
D_ex = elim_Nat^{1+l}( _. Ty l
                     ; ⌜Sum_i ⟦b_i⟧⌝                       -- height 0
                     ; (m, rec. ⌜Sum_j ⟦s_j⟧(El rec)⌝)     -- height m+1
                     ; · )
⟦D⟧  = Σ^{0,l}(h : Nat). El^l (D_ex h)
```

with `l = ⊔` of the field levels as in tier 0, and the `elim_Nat` itself
inlined at each use rather than λ-abstracted (there is no `def` in the
kernel; `def`-is-inlined is the surface's rule too).

**The two height classes partition the constructors, so neither spine needs
padding.** A base constructor has height exactly 0 and cannot appear at a
successor; a step constructor has height ≥ 1 and cannot appear at 0. An
earlier draft carried `Empty` branches to keep one uniform spine across all
heights; that is unnecessary, because `match` splits on the height *first*
(§4) and so never needs the two spines to have the same shape. Each
constructor's tag index is its position among the constructors **of its own
class**.

Degenerate cases:

- `p = 0` (no base constructor) — `D_ex 0 = Empty`, and `⟦D⟧` is uninhabited,
  which is the right answer for a declaration with no finite values.
- `q = 0` — no recursive constructor: that is tier 0, and the classifier
  routes it there.
- `p = 1, q = 1` — `List`: *both* spines are single-branch, so the sum
  disappears entirely and the encoding is just
  `vec 0 = ⌜Unit⌝`, `vec (h+1) = ⌜Σ(a : ⟦A⟧). El rec⌝`. This is why the
  prototype also does `Bits` (§7): `List` alone never exercises a sum spine.

### 3.2 Constructors

Projections are named `height x = fst x` and `payload x = snd x`.

```
⟦b_i(a⃗)⟧    = pair(0;         ι_i(tup(a⃗)))
⟦s_j(a⃗, t)⟧ = pair(S (height t); ι_j(tup(a⃗, payload t)))
```

where `ι` and `tup` are tier 0 §4's injection path and field tuple, taken in
the relevant class's spine, and the recursive field's slot is filled with the
child's **payload**, not the child.

Why this typechecks: the outer pair's second component must inhabit
`El (D_ex (S (height t)))`, which whnf-reduces to the successor spine with
`El rec := El (D_ex (height t))` — exactly the type of `payload t`. No
coercion, no transport.

**The height is `Succ`-headed whatever the child is**, and that is the whole
reason β works on open terms: `D_ex (S (height t))` unfolds even when `t` is
a variable, so the payload's type is exposed, so a `match` on `s_j(a⃗, t)`
reduces. Contrast §8, where the height of a branching constructor is
`S (max …)`, which is `Succ`-headed too — but the *payload* there needs the
comparison of the children's heights to compute, and that is what gets stuck.

Constructors remain macros of fixed arity, not kernel functions (tier 0 §4).

---

## 4. `match` and the eliminator

They are one construction: the derived eliminator, with the induction
hypothesis unused when the surface `match` has no self-call. The
guarded-self-call rule of `issues/match-recursion.md` lowers to *exactly*
the `elim_Nat` recursion variable applied to the child's payload.

Given a motive `M` over `z : ⟦D⟧` at level `l''`:

```
Mot(h)  = Π^{l,l''}(v : El (D_ex h)). M[pair(h; v)/z]          -- over h : Nat
elim(t) = elim_Nat^{l''}( h. Mot(h); base; (m, rec. step); height t )  (payload t)
```

**Base.** `Mot(0) = Π(v : El (D_ex 0)). M[pair(0; v)/z]`; emit
`λ(v : El (D_ex 0)). ⟨nested Case over the base spine⟩`, each arm the
corresponding base-constructor arm body with the fields projected as in tier
0 §5. For `p = 1` with a nullary constructor the spine is `Unit` and the
`Case` disappears: the body is the arm itself, and it checks against
`M[pair(0; v)/z]` with `v` a *variable* — which is where **`Unit` η is
load-bearing**: the arm was written for `M[nil/z] = M[pair(0; ⟨⟩)/z]`, and
conversion identifies the two because `El (D_ex 0) ⇝ Unit` is
proof-irrelevant (`conv.rs:696`). Verified in `append_nil_by_induction`,
whose base case is a bare `refl`.

**Step.** In `(Γ, m : Nat, rec : Mot(m))`, emit
`λ(v : El (D_ex (S m))). ⟨nested Case over the successor spine⟩`, and in the
arm for `s_j`, with `x` the `Case` binder:

```
fields    = tier 0 §5.1's projections of x
tail      = pair(m; the recursive field's projection)
ih        = rec (the recursive field's projection)
arm body  = b_j[fields, tail, ih]
```

The arm's obligation is `M[pair(S m; v)/z]`, and the arm body was written for
`M[s_j(fields, tail)/z]`; those are convertible because
`s_j(fields, tail) = pair(S (height tail); ι_j(…)) = pair(S m; ι_j(…))` and
`ι_j` of the projections of `x` is `x` up to `Case` β and Σ-η. This
composition — motive pushed through the injection *and* through the
repackaging `pair(m; ·)` — is where a lowering bug would hide, the tier-1
analogue of tier 0 §5.2's nested motive.

**Scrutinee.** The recursion is applied to `payload t`, at
`Mot(height t) = Π(v : El (D_ex (height t))). M[pair(height t; v)/z]`, whose
instance at `payload t` is `M[pair(height t; payload t)/z] ≡ M[t/z]` by Σ-η.

`n = 0` arms (`absurd`) and exhaustiveness are surface obligations as in tier
0; note that the arm list is split by class before lowering.

---

## 5. No-confusion

### 5.1 Disjointness, different height classes

`nil` versus `cons`: the heights differ in *shape* — `0` against `S _` — so
no payload analysis is needed at all. With

```
zero_pred = elim_Nat^1(_. Ty 0; ⌜Unit⌝; (_ _. ⌜Empty⌝); ·)
```

a single `J` on `e : Id(⟦D⟧; b_i(a⃗); s_j(b⃗))` at motive
`(y p. El (zero_pred (height y)))` with `case = ⟨⟩` lands in `Empty`:
`zero_pred (height b_i(a⃗)) ⇝ zero_pred 0 ⇝ ⌜Unit⌝` and
`zero_pred (height s_j(b⃗)) ⇝ zero_pred (S _) ⇝ ⌜Empty⌝`, both
definitional. Then `ElimEmpty` to the user's goal.
(`no_confusion_nil_versus_cons`.)

### 5.2 Disjointness, same height class

`B0 x` versus `B1 y` have the *same* height shape, so §5.1 cannot fire — the
prototype's negative control checks that it does not
(`the_kernel_gate_rejects_the_near_misses` case 3). Here the tag predicate
comes back, but as a **function of the height**, because the payload's type
depends on it:

```
is_c = elim_Nat^1( h. Π^{l,1}(v : El (D_ex h)). Ty 0
                 ; λv. ⌜Empty⌝                        -- other class
                 ; (m, rec. λv. ⟨Case over the spine: ⌜Unit⌝ at c, ⌜Empty⌝ else⟩)
                 ; height x ) (payload x)
```

The `elim_Nat` motive is a Π *into* `Ty 0`, at level `1` — tier 0's large
elimination, one binder deeper. Then `J` at `(y p. El (is_c y))` with
`case = ⟨⟩`, exactly as in tier 0 §6.1. (`bits_no_confusion_at_the_same_height`.)

Two base constructors of the same declaration are tier 0 §6.1 verbatim,
under the `height`-0 branch.

### 5.3 Injectivity

Unchanged in shape from tier 0 §6.2: build a *total* projection for the field
by the derived eliminator with the left-hand side's own field value as the
default in every other branch — keeping the motive constant — then `J` at
`(y p. Id(field type; a_k; proj y))` with `case = refl`.

Two tier-1 specifics:

- For the **recursive** field the projection returns `⟦D⟧`, and the arm must
  repackage: `pair(m; the child's payload)`, not the payload. The default in
  the base branch is the left-hand side's own child.
- The **side condition is tier 0's** (§6.2): a field whose type mentions an
  earlier field of the same constructor is diagnosed, not derived. The
  recursive field itself is never dependent, so it is always in reach.

(`no_confusion_cons_is_injective` derives both `a = a'` and `l = l'` from
`cons a l = cons a' l'`.)

---

## 6. Worked example: `inductive List<A> { Nil, Cons(A, List<A>) }` at `A = Nat`

Tag elided, as everywhere here.

```
vec 0        = ⌜Unit⌝
vec (m+1)    = ⌜Σ(a : Nat). El rec⌝                    -- rec = vec m, as a code
List Nat     = Σ(h : Nat). El (vec h)

nil          = pair(0; ⟨⟩)
cons a l     = pair(S (fst l); pair(a; snd l))

elim(z. M; u; a t ih. w; s)
  = elim_Nat^{l''}( h. Π(v : El (vec h)). M[pair(h; v)/z]
                  ; λv. u
                  ; (m, rec. λv. w[ fst v
                                  , pair(m; snd v)
                                  , rec (snd v) ])
                  ; fst s ) (snd s)
```

`append xs ys` is that eliminator with `M := List Nat` constant, `u := ys`,
`w := cons a ih`; the prototype checks `[1,2] ++ [3] ≡ [1,2,3]`,
`append xs nil = xs` and `(xs ++ ys) ++ zs = xs ++ (ys ++ zs)` by induction
(the step case in both is one `cong` — `J` at
`(y p. Id(List; cons a l; cons a y))`), and the two no-confusion lemmas.

`Bits`, the multi-constructor case, differs only in the spines:

```
spine 0      = ⌜Unit⌝                                  -- Nil
spine (m+1)  = ⌜El rec + El rec⌝                       -- B0 | B1
B0 x         = pair(S (fst x); inl(payload x))
B1 x         = pair(S (fst x); inr(payload x))
```

and its `match` is `elim_Nat` on the height with a `Case` on the payload
inside the step. `flip (flip x) = x` by induction is the prototype's
exercise of both step arms.

---

## 7. Cost

Per value: one `Nat` height (unary, so a list of length `n` carries an
`n`-deep numeral — the same asymptotics as the spine itself) plus tier 0's
per-constructor tag and `Unit` terminator. Per *type occurrence*: the whole
`elim_Nat` is inlined, so a type mentioning `List Nat` carries the family's
definition each time. Both are acceptable for now and both are the kind of
thing a later `def`-in-the-kernel or universe-polymorphic abstraction would
fix; neither affects conversion behaviour, only term size.

---

## 8. What this scheme does not cover

### 8.1 Branching constructors — an open decision, not a coding task

A constructor with two or more recursive fields (`Node(Tree, Tree)`, and
therefore the IR expression knot of `issues/ir-simulate-design.md`) does
**not** lower by this scheme, and the reason is worth writing down, because
the issue's committed plan ("max+1 for trees; always computable in the
finitary tier") is right about the height and wrong about the consequence.

The height *is* computable: `S (max h_l h_r)`. The problem is the payload.
At height `m+1` the two children have heights `h_l, h_r ≤ m` with
`max = m`, so the branch type has to be a *disjunction of shapes* —
"left exactly `m`, right at most `m`" or "left at most `m-1`, right exactly
`m`" — and "at most" is itself a family. The cleanest form of that is a
simultaneous recursion producing both the exact family and the sum of all
smaller ones:

```
(D_ex, D_below) : Nat → Σ(Ty l)(Ty l)
D_ex 0        = ⌜Sum_i ⟦b_i⟧⌝                   D_below 0     = ⌜Empty⌝
D_below (m+1) = ⌜El (D_ex m) + El (D_below m)⌝   -- "height ≤ m", canonically
D_ex (m+1)    = ⌜(D_ex m × D_below (m+1)) + (D_below m × D_ex m)⌝   -- for Node
```

which is well-defined (each side at `m+1` needs only the pair at `m`),
canonical (a value's height picks its summand, so there is no padding), and
generalizes to `r` recursive fields as an `r`-way sum. The eliminator comes
out of the same simultaneous recursion, since
`D_below (m+1) = D_ex m + D_below m` means the handler for `D_below` is a
`Case` of the two handlers at `m`.

**And it still fails, on β.** To build `node l r` we must inject the shorter
child into `D_below`, at a depth that is the *difference* of the children's
heights — so the constructor is not a fixed term but a case-split on the
comparison `h_l` vs `h_r`, and an embedding function recursive on the
difference. With concrete children everything computes; with an open child
the comparison is stuck, so `node l r` is not in constructor form, so
`match (node l r) { … }` does **not** reduce. That kills the property §3.2
buys for `cons` and that every proof by `match` on an open scrutinee needs.

The same wall stands in front of the other measures — total size (needs the
split point, hence a convolution over a table of all smaller families),
preorder-token vectors (needs concatenation, stuck on open children), Gödel
numbering of the shape (needs pairing arithmetic, stuck at the index) — and
the shape of the argument is always the same: when the parent's payload type
is not *literally* a container of the children's payload types, assembling it
takes computation on measures, and that computation is what gets stuck. For
`≤ 1` recursive field it is literally a container, which is exactly why the
linear fragment is clean.

The routes out, for the decision this needs:

- **(a) Branching goes to tier 2** — `W` + `Id` + funext-as-axiom, as
  `issues/kernel-v1-extensions.md` already argues for infinitary types. Costs
  the definitional β of `match` on branching data (W's children are
  functions, so `leaf`'s canonical form is not unique up to conversion) and
  makes the IR's equational reasoning propositional. Cheapest to build, most
  expensive to use.
- **(b) Multi-index fording** — index the family by a *shape* rather than a
  `Nat` (a pair of heights for a binary node), so the parent's payload type
  is literally the children's. The index type is then itself a branching
  inductive, which is circular unless the shape is fixed *statically*, i.e.
  a per-depth stratification. Needs real design work; would preserve β.
- **(c) Accept the stuck constructor** with a normalization discipline: keep
  the `Below` scheme, and have the elaborator emit the *canonical* embedding
  when the heights are literals and postpone otherwise. Restores computation
  in the common closed case, leaves open-scrutinee proofs to propositional
  reasoning. Cheap, partial, and hard to explain.

My recommendation is **(b), with (a) as the fallback that unblocks the IR
now**: the IR's tree-shaped expressions are exactly what we simulate and
prove about, so their `match` really does want to compute on open terms; but
`W` is already in the kernel and already argued sound, so the IR need not
wait for the design.

### 8.2 Mutual and nested recursion

`Rose { Node(List<Rose>) }` and mutually recursive declarations need a
simultaneous family — the same `elim_Nat`-returning-a-Σ-of-codes device as
§8.1's `(D_ex, D_below)`, which is unproblematic here since it is not the
part that breaks. Deferred only because nothing needs it yet.

### 8.3 Parameters

Monomorphized, as in tier 0 §2: `List<Nat>` and `List<Bool>` lower to two
unrelated families. The prototype is at `A = Nat` and the scheme's `⟦A⟧`
appears in exactly one place (the code `⌜A⌝` in the field spine), so nothing
here blocks the universe-polymorphic version later.

### 8.4 Indices

Fording an index means an `Id` equation as a constructor field, and `Id` has
no η — so the tier-0 §3.3 hazard (a neutral field where conversion needs a
canonical one) returns with teeth. The scheme above deliberately contains no
`Id`, and indexed finitary families should be designed against that
constraint in their own round rather than bolted on here.

---

## 9. Acceptance checklist

Each item is a test in `crates/elab/tests/tier1_fording.rs`; all pass as of
2026-07-24, at `List<Nat>` and `Bits`.

1. The type, every constructor, and every derived lemma pass the real kernel
   check (`the_type_and_the_constructors_check`,
   `bits_type_constructors_and_computation`).
2. Heights are exact and compute: `height [1,2,3] ≡ 3`
   (`heights_are_exact_and_computed`).
3. Canonical forms are unique — equal values convertible, different values
   not, including same-length/different-content and prefix cases
   (`canonical_forms_are_unique`).
4. A constructor applied to an **open** child still typechecks
   (`cons_on_an_open_tail_checks`) and still β-reduces under a `match`
   (`cons_beta_fires_on_an_open_element_and_tail`, and `flip (B0 x)` in the
   `Bits` test).
5. A recursive function defined by the derived eliminator computes on closed
   arguments and is neutral-but-typed on open ones
   (`append_checks_and_computes`, `append_on_an_open_argument_is_neutral_but_typed`).
6. Proofs by induction with an `Id` motive check: `append xs nil = xs`,
   `(xs ++ ys) ++ zs = xs ++ (ys ++ zs)`, `flip (flip x) = x`
   (`append_nil_by_induction`, `append_assoc_by_induction`,
   `flip_flip_is_identity_by_induction`).
7. Disjointness across height classes (`no_confusion_nil_versus_cons`) and
   within one (`bits_no_confusion_at_the_same_height`).
8. Injectivity per field, including the recursive field
   (`no_confusion_cons_is_injective`).
9. Negative controls: `refl` does not prove an induction, a step case that
   conses the wrong element is rejected, and the height-shape disjointness
   argument does not fire between two uses of the same constructor
   (`the_kernel_gate_rejects_the_near_misses`).

What the checklist does **not** cover, and the generator must add: the
nominal tag (elided in the prototype, mechanical from tier 0 §3.3),
parameters other than `Nat`, spines with more than two constructors per
class, and fields at levels above 0.
