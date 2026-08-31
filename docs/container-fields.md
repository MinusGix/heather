# Container fields: `Rose` and the surface vector type

Status: **phases 1 and 2 implemented 2026-07-26.** `container_fields.rs` +
`vector_types.rs` are §8's checklist; `container_recursion.rs` is §4.2's
(17 tests total, plus 7 kernel-level ones on the schemas in
`crates/elab/src/vec.rs`). §9 records what implementing found. Written before
the code, per the discipline of `docs/inductive-tier0-lowering.md` and
`docs/inductive-tier1-wf-lowering.md`. Tracking issue:
`issues/nested-inductives-container-fields.md`.

This closes the gap `docs/inductive-tier1-wf-lowering.md` §8.1 names: `Rose`
is unwritable, not because the kernel lacks anything, but because the surface
has no way to *say* "the children are a vector".

The kernel side is done and not speculative: `Type::Vec`, `Type::Fin`,
`term::nth` and the whole `Wf` former exist and are exercised by
`crates/kernel/tests/{vec_fin,wf}.rs`. `Wf`'s arity has always been a **term**
with the shape free (`wf-former-design.md` §1.3), precisely so it could be
data rather than a literal. This document is the surface and lowering work
that finally uses that.

---

## 1. The idea in one line

> **The length is an ordinary payload field, and the container field is a
> vector at that length.**

```heather
inductive Rose { Node(label: Nat, len: Nat, kids: [Rose; len]) }
```

`len` is a perfectly ordinary `Nat` field: it goes in the shape, exactly where
tier 1 already puts payload fields. The arity term `n`, which tier 1 computes
as a literal per constructor, instead *projects `len` out of the shape*. And
then `⟦Rose⟧ = Wf^l(x : S). n` with

```
S = Σ(#tag). Σ(label : Nat). Σ(len : Nat). Unit⁰
n = case x of  inl c ⇒ fst (snd (snd c))          -- i.e. `len`
```

which is `wf-former-design.md` §7's `S = Σ(a : A). Nat`, `n = snd x`, reached
from a surface declaration. No `List`, no conversion between a user container
and the kernel's `Vec`, and therefore none of §8.1's β-on-open-subterms
problem: the container in the source **is** the `Vec` in the kernel.

## 2. What the surface gains

### 2.1 The vector type `[T; n]`

```
ty_atom ::= … | '[' ty ';' expr ']'
```

`[T; n]` elaborates directly to `Type::Vec { level, elem: ⟦T⟧, len: ⟦n⟧ }`,
with `n` checked at `Nat`. It is a **primitive indexed type**, not a
user-declared one — there is no fording and no encoding, which is why it can
be added without touching the inductive tiers.

Not `[T]` with the length hidden: the length has to reach the shape (§3), and
a surface that hides it would have to invent an existential and immediately
lose the computation this is all for. Hiding it is sugar to consider later
(§7), not the primitive.

### 2.2 Collection literals `[a, b, c]`

```
atom ::= … | '[' (expr (',' expr)*)? ']'
```

Checking-only and selected by the expected container type through the
canonical prelude class:

```heather
class CollectionLiteral<C>(n: Nat) {
    element: Type,
    fromLiteral: [element; n] → C,
}
```

The expected `C` and syntax-known length `n` determine a dictionary;
`element` supplies the expected type for every written entry, including when
the literal is empty, and `fromLiteral` receives the already-checked primitive
vector. This bulk boundary makes ordering and duplicate policy an instance's
visible implementation choice. `List<T>` right-folds that vector into
`Nil`/`Cons`. Primitive `[T; n]` is the intrinsic bootstrap reading, analogous
to `Nat`'s intrinsic numeral reading; user containers use the class.

For primitive vectors, `n` must still be a **literal** and equal the expected
length. `[]` is `⟨⟩ : Unit^l`; `[a, b]` is
`pair(a, pair(b, ⟨⟩))`, built against the Σ-chain that `Vec(T; 2)` unfolds to.
With no expected container the spelling is ambiguous and does not default.

This is the one place `,` and `[` meet, and it is exactly why lambdas take
`=>` and not `,` (`docs/surface-function-types.md` §1.2): `[λ (x: Nat), f(x), g]`
would have been ambiguous. With `=>` it is not.

## 3. The lowering

Everything in `docs/inductive-tier1-wf-lowering.md` carries over; this section
states only the deltas.

### 3.1 Classification

A constructor field is now one of **three** kinds, not two:

| kind | written | contributes |
|---|---|---|
| payload | any type not mentioning `D` | a Σ component of the shape |
| plain recursive | `D` (uniform, direct — tier 1 §1) | one child |
| **container recursive** | `[D; e]` | `⟦e⟧` children |

**Restrictions, each diagnosed (§6):**

- **At most one container field per constructor**, and it must come **last
  among the child-contributing fields**. Two containers would need the
  children tuple split at a computed index, which needs recursion on the first
  length — the tuple has no such operation. A plain recursive field *after* a
  container is unprojectable for the same reason: reaching it means skipping
  `⟦e⟧` elements.
- **`e` may mention only payload fields declared before this one.** It is
  evaluated *inside the shape*, where nothing else exists. A recursive field
  is not in scope in later field types anyway (tier 1 §2), so this adds no new
  restriction beyond "not a later payload field either".
- **Phase 1 narrows that further: `e` must be a bare payload field *name*.**
  `[Rose; len]` yes, `[Rose; add(a, b)]` rejected with a message. The reason
  is not difficulty but reuse: at a bare name the arity branch is exactly the
  projection `ConstBody::Field` already builds for no-confusion, so the two
  cannot drift. A general expression means elaborating a surface term against
  the shape's Σ spine, which is a *third* place that has to agree about
  payload indices, and it is additive later.

### 3.2 The shape `S` — unchanged

Container fields contribute nothing to `S`. Their length already does, as an
ordinary payload field, which is the whole trick. `lower_ctor` needs one more
"skip this field" case and nothing else.

### 3.3 The arity `n` — the only real change

Tier 1 §3 builds `n` as a constant case tree returning each constructor's
literal `mᵢ`. Now, at constructor `i` with `kᵢ` plain recursive fields and an
optional container of length `e`:

```
n_i  =  Succ^{kᵢ}( ⟦e⟧[shape projections] )         with a container
n_i  =  Succ^{kᵢ}( Zero )   ( = the literal kᵢ )    without one
```

so the existing literal case is the `e`-absent instance of the same formula,
and the two do not diverge. `⟦e⟧` is elaborated against the *shape's* Σ spine:
each payload field name resolves to `fst (snd^{j+1} c)`, the same projection
tier 0 §5.1 aliases into an arm body.

**`Succ`-headed is load-bearing.** `Vec(T; Succ p) ⇝ Σ(_ : T). Vec(T; p)` for
*any* `p`, neutral included (`reduce.rs:147`), so `Succ^{kᵢ}(⟦e⟧)` unfolds
exactly `kᵢ` times and stops with the tail `Vec(T; ⟦e⟧)`. That single fact is
what makes §3.5 work.

### 3.4 Constructors

`cs : Vec^l(⟦D⟧; n[ℓᵢ/x])` is the plain children *followed by* the container:

```
cs  =  pair(r₁, pair(r₂, … pair(r_{kᵢ}, xs)))
```

where `xs` is the container argument, already a `Vec^l(⟦D⟧; ⟦e⟧)`. Tier 1
terminates the tuple with `⟨⟩ : Unit`; here the terminator is *the container
itself*, and `Unit` is just the `e = 0` case of that. So the tuple builder
takes a "tail" argument and tier 1 passes `⟨⟩` — again one code path, not two.

The `snd_ty` annotation caveat of tier 1 §5 applies unchanged and matters
more here: the tail type is `Vec^l(⟦D⟧; k)` scoped **under** the pair's first
component.

### 3.5 What an arm binds

| surface binder | lowering | type |
|---|---|---|
| payload field `j` | `fst (snd^{j+1} c)` | its declared type |
| plain recursive, the `t`-th | `nth^l(⟦D⟧; n; cs'; ι_t)` | `⟦D⟧` |
| **container** | `snd^{kᵢ} cs'` | `Vec^l(⟦D⟧; ⟦e⟧)` |

The container binder is *literally the tail of the children tuple* — no `nth`,
no index arithmetic, one `snd` per preceding plain child. It typechecks
because §3.3 made the arity `Succ`-headed exactly `kᵢ` times.

Note what this buys: the container binder is a **real vector value**, not an
accessor or a fold-only opaque. It can be returned, passed, and compared.

## 4. Eliminating a container — the phases

Declaring and constructing `Rose` is phase 1. *Recursing* over one needs more,
and it is worth being explicit that this splits into three problems of very
different difficulty rather than pretending one round covers them.

### 4.1 Phase 1 — declare, construct, project (this round)

`Rose` declares, `Node(1, 2, [a, b])` checks, `match` binds `kids` as a
vector, closed values compute and compare, no-confusion works. What is *not*
yet writable is a function that recurses into the children.

That is a real limit and it is why phase 2 is scoped immediately below rather
than left vague. But phase 1 is not half a feature: it is the whole
type-and-data story, it is what `wf-former-design.md` §7 claimed and never
demonstrated, and every later phase is an *elimination* form layered on the
same encoding.

### 4.2 Phase 2 — `map`/`fold`, and the self-call over a container

**Implemented 2026-07-26**, as designed below. `crates/elab/src/vec.rs` holds
the three schemas with their own kernel-level tests; the surface forms are
`map`/`fold` builtins in `elab_infer`, and `GuardKind::Wf` gained a
`ContainerIh` so a self-call can find the container it belongs to.

Two primitives, both `elim_Nat` on the length (the same shape as `term::nth`,
which is already an `elim_Nat` schema):

```
map    : Π(n : Nat). Vec(A; n) → (A → B) → Vec(B; n)
fold   : Π(n : Nat). Vec(A; n) → B → (A → B → B) → B
```

and then the question that actually matters: **how does the induction
hypothesis reach the children?**

The ih the kernel hands a `Wf` arm is `ih' : Π(i : Fin n). M[nth cs i / z]` —
an *indexed function over the children*, which is exactly a "vector of
results" waiting to be tabulated. So the natural surface form is a self-call
whose argument is the container binder:

```heather
fn size(r: Rose) -> Nat {
    match r {
        Node(label, len, kids) =>
            Succ(kids.map(size).fold(0, λ (a: Nat) (b: Nat) => add(a, b))),
    }
}
```

`kids.map(size)` is recognized *syntactically* — receiver is exactly a
container binder, function is exactly the self-name — and elaborates to the
tabulated ih, never to a real `map` over a real function value. That keeps the
rule the guard already enforces: a self-call is the ih, and it exists only in
the positions the eliminator provides. `tabulate : Π(n). (Fin n → A) → Vec(A; n)`
is the third `elim_Nat` schema, and `kids.map(size)` is `tabulate(len, ih')`.

The alternative — let `size` be an ordinary function value passed to a real
`map` — cannot work, and the reason is worth recording: there is no fixpoint
and no `rec`, so the self-name is *not a value*. It exists only as the
eliminator's ih. That is the design of `issues/match-recursion.md`, not an
accident of this round.

### 4.3 Phase 3 — proofs over a container

`mirror(mirror(t)) = t` over `Rose` needs a **dependent** fold: the ih at
index `i` proves `M[kids[i]]`, and combining `n` of those into `M[Node …]`
is the classic nested-induction problem. The honest options (an `All`
predicate over a vector, or a pointwise-equality lemma plus `Vec`
extensionality) are a design round of their own and are **not** designed here.

**Designed 2026-07-26 in `docs/container-proofs.md`**, which takes the second
option: one more `elim_Nat` schema (`tab_cong`) plus a typing rule for the
self-call at an `Id` motive, no `All` and no kernel change. `All` is definable
— codes and `El` give large elimination — but nothing at the surface can
*eliminate* a vector, so it would be evidence no proof could consume.

Phase 1's tests should therefore not pretend: no theorem below is proved *by
induction over a container*, and the acceptance checklist says so.

## 5. Level

`Vec`'s level is its element's, and `Wf`'s is its shape's. A container field
of `[D; e]` contributes `⟦D⟧`'s level, which is the shape's level, so nothing
inflates. The `len` payload field is a `Nat` at level 0 and contributes
nothing. Nothing in this scheme assumes level 0 — as with tier 1, the level is
taken from the shape throughout — but nothing at the surface can reach a
nonzero one yet either (tier 1 §8, polymorphic containers).

## 6. Rejections

Each diagnosed, never mis-lowered — the hazard class
`docs/inductive-tier0-lowering.md` opens by naming.

| Written | Message |
|---|---|
| two container fields in one constructor | "a constructor may have at most one container field: the children are one tuple, and splitting it at a computed length is not an operation it has" |
| a plain recursive field after a container | "a recursive field may not follow a container field: reaching it would mean skipping `n` children" |
| `[D; e]` with `e` not a bare payload field name | "a container field's length must be the name of a payload field declared before it (docs/container-fields.md §3.1)" |
| `[T; n]` for `T` mentioning `D` but not *being* `D` | tier 1 §1's nested-recursion message, unchanged |
| a vector literal at a non-literal expected length | "a vector literal needs a literal length here; `xs` of length `n` has to come from a binder" |
| a vector literal of the wrong length | "this vector literal has `k` elements but `m` are expected" |
| a collection literal with no expected type | "a collection literal needs an expected container type (it is checking-only, like `refl`)" |
| `xs.map(f)` on a non-vector | "`map`'s receiver has to be a vector" |
| a self-call `xs.map(f)` where `xs` is not *the* container binder | "a recursive call over a vector has to be over the container field bound by the enclosing `match`" |
| a self-call over a container at a **dependent** result type | "recursing over a container field needs the result type to be independent of its argument … (§4.3)" — this is the phase-3 boundary, and it is a rejection rather than a silent mis-elaboration |
| `map`'s function at a dependent result type | "the result is a vector, whose elements all have one type" |
| `inj` at a container field | "its type `[D; …]` depends on the length field before it, so the two sides' lengths would have to be definitionally equal" — see §9.2 |

## 7. Deliberately not in phase 1

- **Inferring the length field.** `Node(1, [a, b])` with `len` implicit and
  solved from the literal. Wants `{}`-implicit *fields*, which is the same
  machinery as `issues/implicit-binders-in-function-types.md`.
- **`Fin n` and `xs[i]` at the surface.** Indexing only computes at a literal
  length, so it buys little before phase 2, and `xs[i]` was already earmarked
  for the trait/indexing layer (`issues/goal-holes.md`'s deferred list).
- **A vector type whose length is hidden** (§2.1).
- **Nested containers** (`[[D; m]; n]`): the children tuple is flat.
- **Containers of a *different* inductive** (`[List; n]` inside `Rose`) —
  that is an ordinary payload field of vector type and should just work, but
  it is not what this round is for and is not tested as a supported case.

## 8. Acceptance checklist (phase 1)

1. `[T; n]` parses in every type position, and `[T; 0]` / `[T; 2]` elaborate
   to `Type::Vec` and kernel-check.
2. `[]` and `[a, b]` check against `[T; 0]` / `[T; 2]`; the wrong length and
   the missing expected type are rejected (§6).
3. `inductive Rose { Node(label: Nat, len: Nat, kids: [Rose; len]) }` declares
   and `⟦Rose⟧` kernel-checks as a `Wf` whose arity projects `len`.
4. `Node(7, 0, [])` and `Node(7, 2, [a, b])` check at `⟦Rose⟧`, including with
   *open* children.
5. `match r { Node(l, n, kids) => … }` binds `kids` at `[Rose; n]`, and
   returning it typechecks. β fires on a constructor form with open children.
6. A constructor mixing a plain recursive field with a container
   (`Both(t: Rose, len: Nat, kids: [Rose; len])`) lowers, and both binders
   project correctly — the `Succ`-headed arity of §3.3.
7. Tier 1 is unchanged: `Tree`/`List` still lower, still compute, and the
   whole existing suite passes.
8. No-confusion still works on a declaration with a container field.
9. Every §6 rejection, with its message.
10. **Honesty item.** No test claims induction over a container. Phase 2 is
    what makes that writable, and §4.3 is why the proof case is harder still.

---

## 9. What implementing phase 1 found

### 9.1 The classification predicate silently dropped every container

`Inductive::recursive` — the one predicate that decides whether a declaration
lowers to a `Wf` at all — was `ctors.iter().any(|c| c.arity() > 0)`. Once
`arity()` came to mean *plain* children, a constructor whose only recursive
field is a container has `arity() == 0`, so

```heather
inductive Rose { Node(label: Nat, len: Nat, kids: [Rose; len]) }
```

was classified **non-recursive**, lowered to a bare tier-0 sum-of-Σs, and its
children were **discarded**. `⟦Rose⟧` was a record of `(label, len)`.

That is the hazard class this document's tier opens by naming — not a
rejection, a checked theorem about a type nobody wrote. And it is worth being
precise about how close it came: **every positive test in §8 passed against
the broken encoding.** `Node(7, 2, [a, b])` checked, `match` bound `kids`,
`rebuild` round-tripped, no-confusion worked. They had to: dropping a field
makes a *smaller* type, and nothing that only builds and projects can tell.

What caught it was writing the **negative** control:

```heather
theorem collapsed(a: Rose, b: Rose): Node(0, 1, [a]) = Node(0, 1, [b]) { refl }
```

which must be rejected and was accepted, because with the children gone the
two nodes were literally the same term. That test is
`container_fields::a_container_is_not_dropped`, and its comment says why it
exists.

This is the third time in this codebase that a live defect was invisible to
every positive test and one negative observation found it —
`unit-level-and-vec-preservation`, `tyvar-scoping-in-lowered-fields`, now
this. The pattern is not "write more tests"; it is that a positive test
cannot distinguish a type from a *quotient* of it.

### 9.2 `inj` at a container field is a dependent-field problem

Not a missing case. The field's type is `[D; len]`, which depends on the
field before it, so injectivity's constant motive would need both sides'
lengths definitionally equal. That is exactly tier 0 §6.2's restriction on a
payload field whose type depends on an earlier one, and it should be lifted
the same way and at the same time — so it is diagnosed here rather than
special-cased. Disjointness (`absurd`) is unaffected and works.

Tracked as `issues/dependent-field-injectivity.md`, filed *because* of this
second instance: one restriction with two instances wants a shared fix, and
the issue records the wrinkle that makes it a design question rather than a
patch — the transport route makes `inj` state a **heterogeneous** equation
(`kids_a = transport(…, kids_b)`), and whether that is the API we want has
not been decided. Note the container case is the more likely one to be hit:
a dependent payload field is unusual, a container field is dependent by
construction.

### 9.3 Two smaller corrections

- **`read_ctor`'s payload walk was `fields.len() - arity()`.** With three
  field kinds, payload and *plain* children no longer partition the fields, so
  a container constructor read one field too many and no-confusion reported
  "not a constructor application". Now `payload().count()`.
- **A vector literal's expected length needed reducing, not matching.** A
  container's expected length arrives as a projection out of the label
  (§3.4) — it *computes* to a numeral rather than being one. `elab_vec_lit`
  now whnf's the length first. It also must **not** whnf the expected *type*:
  `Vec(T; 0) ⇝ Unit` and `Vec(T; 2)` a Σ-chain, so the `Vec` it is looking for
  would be gone.

### 9.4 What phase 1 does not do, restated honestly

No function in the test suite recurses into a container's children, because
none can be written yet (§4.2). `Rose` is declarable, constructible,
matchable and comparable; it is not yet *foldable*. The one thing phase 1
should not be read as claiming is that `Rose` is usable for programming.

## 10. What implementing phase 2 found

### 10.1 The step of an `elim_Nat` schema proves `M(S k̂)`, not `M(k̂)`

Both `map` and `fold` had their step's λ domain as `Vec(A; k̂)` where it must
be `Vec(A; S k̂)` — the step *proves* `M(S k̂)`, and that is precisely what
makes the `fst`/`snd` in its body legal, since `Vec(A; S k̂) ⇝ Σ(_ : A).
Vec(A; k̂)`. `tabulate`, written last, had it right.

Caught in seconds because the schemas were kernel-tested **before** any
surface syntax reached them (`crates/elab/src/vec.rs`'s test module). Through
three layers of elaboration the same bug would have surfaced as an opaque
`NotConvertible` on a `Rose` program. The general lesson is the tier-1 one: a
generated term wants a test at the level it is generated, not only at the
level it is used.

### 10.2 `strengthen` needs no occurrence traversal

Phase 2 has to decide whether a motive depends on the scrutinee — a container
maps to a *vector* of results, which only types when the result type is
independent of the child (§4.3). Rather than a fourth hand-written traversal
over the syntax, `vec::strengthen` substitutes `Zero` for the variable and
weakens back: that round trip is the identity exactly when the variable did
not occur, because `shift_local` moves *variables* and leaves the `Zero` that
replaced any occurrence behind. Two existing `subst.rs` operations, no new
code over the term grammar — which matters, because a traversal that forgets
a former is a silent wrong answer.

### 10.3 The self-call over a container is a *lifting*, and reads as one

`kids.map(size)` has `size : Rose → Nat` applied to `kids : [Rose; len]`. The
types do not line up under any ordinary rule, and they are not meant to: this
is the induction hypothesis, which the eliminator hands over as
`Π(i : Fin n). M` — an index function — and `tabulate` turns into data. It is
recognized syntactically (receiver is *the* container binder, function is
exactly the self-name) and elaborates to nothing else.

The alternative, letting `size` be an ordinary value passed to a real `map`,
cannot work and it is worth restating why: there is no fixpoint and no `rec`,
so **the self-name is not a value**. It exists only as the eliminator's ih.
That is `issues/match-recursion.md`'s design, not an accident here.

Note the offset that a mixed constructor forces: with `m` plain children the
ih is indexed by `Fin (Succ^m len)` and the container's indices start at `m`,
so the index map is `m` `inr`s. `a_plain_child_and_a_container_recurse_together`
pins it with an asymmetric tree, which is what would catch an off-by-one that
a symmetric one cannot.

### 10.4 Two shift bugs, found later, that phase 2 could not see

Recorded here because they are *phase 2's* code:
`tabulate`'s index-function type shifted its element type one too few (invisible
at a closed element type — every test used `Nat`), and the plain child's ih
annotation in a container constructor never shifted the length (invisible while
only *computation* was tested, since β never compares the annotation). Both are
`docs/container-proofs.md` §10.1–10.2.

### 10.5 Phase 3 remains, and is now a diagnostic rather than a silence

A proof by induction over a container — `kids.map(refl_all)` at a dependent
motive — is rejected with a message naming §4.3. That is the honest boundary:
the ih at index `i` proves `M[kids[i]]`, and combining `n` of those into
`M[Node …]` needs an `All`-predicate or a pointwise-equality story that has
not been designed.
