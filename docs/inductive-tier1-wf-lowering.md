# Tier-1 inductive lowering: branching constructors on the `Wf` former

Status: **implemented**, 2026-07-26 — `crates/elab/src/wf.rs` mechanizes this
document section by section, and `crates/elab/tests/inductive_tier1.rs` is
§10's checklist. Written before the code, per the tier's discipline; §7
records the one place where writing the code corrected the scheme.
Tracking issue: `issues/wf-former.md` (phase 5). This document replaces
`docs/inductive-tier1-lowering.md` (exact-height fording) as *the generator's*
scheme — see §9 for what happens to that document and its prototype.

The kernel side is done and is not speculative: `Type::Vec`, `Type::Fin`,
`Type::Wf`, `Term::Supf`, `Term::ElimWf` and `term::wf_step_telescope` all
exist and are exercised by `crates/kernel/tests/{vec_fin,wf,wf_codes}.rs`.
The rules they implement are `docs/wf-former-design.md`; the decision to have
them at all is `docs/branching-inductives-choice.md` §15. What is *new* here
is only the lowering: surface declaration → those formers.

Conventions are tier 0's (`docs/inductive-tier0-lowering.md`): `⟦T⟧` for the
lowering of a surface type, `Γ` for the ambient local context, kernel
constructor and field names from `crates/kernel/src/term.rs`. Everything in
tier 0 §2 (declaration form, monomorphized parameters, type-argument
inference) and §3.3 (the nominal tag) carries over unchanged and is not
repeated.

Hazard class is tier 0's, and this is why the document comes first: a bug in
a lowering does not produce a rejected term, it produces a **checked theorem
about a type the user did not write**. The kernel cannot catch that. Review
of this document is what catches it.

---

## 1. Scope, and the classification that decides it

A declaration is **tier 1** when some constructor field is a *recursive
occurrence* of the declaration itself. This document covers exactly the
**uniform, direct** case:

```
recursive occurrence  ::=  D<p₁, …, p_k>     -- the declaration's own
                                              -- parameters, in order
```

Everything else that mentions `D` inside a field type is **rejected**, with
its own message, rather than lowered:

- **Nested** (`Rose { Node(A, List Rose) }`): `D` under another type
  constructor. The former *types* it — the shape is `Σ(a : A). Nat` and the
  arity is `snd x`, so the child list is the `Vec` — but lowering a
  declaration whose field type is a user-declared `List` is not a generator
  tweak, and §8.1 says why: it would cost β on open subterms, which is the
  property this tier exists for.
- **Non-uniform** (`D<Nat>` inside `D<A>`): a genuinely different
  monomorphic instance, which the tier-0 rule "parameters are
  monomorphized" cannot express recursively at all.
- **Negative** occurrences: unwritable today (the surface has no function
  type), and the strict-positivity refinement lands when it becomes
  writable.

Non-recursive declarations keep the tier-0 path *verbatim*. The two tiers
are distinguished by one predicate on the declaration, computed once at
declaration time (`Inductive::recursive`), and every site below that says
"tier 1" is guarded by it.

Notation for the rest of the document, for constructor `Cᵢ` of `D`:

- `p̄ᵢ` — its **payload** fields, in declaration order: those that are not
  recursive occurrences.
- `mᵢ` — its **arity**: how many recursive occurrences it has.
- The two interleave in the surface declaration; the lowering separates
  them and each half keeps its own declaration order.

## 2. The shape `S`

> **`S` is tier 0's lowering of `D` with the recursive fields deleted.**

That is the whole rule, and it is deliberate: it means the shape is built by
the *same* `lower_ctor`/`lower_instance` code, given one extra flag, so a
divergence between the two tiers' payload handling is impossible rather than
merely unlikely.

```
⟦Cᵢ⟧ = Σ(#tag : tag_type(D)). Σ(p̄ᵢ). Unit⁰          -- tier 0 §3.1, §3.3
S    = ⟦C₁⟧ + (⟦C₂⟧ + … ⟦C_n⟧)                       -- tier 0 §3.2
```

with `S` at level `l = ⨆ᵢ level(⟦Cᵢ⟧)`, and `S = Empty⁰` when `n = 0` (a
declaration with no constructors is not recursive, so it never reaches here).

Two consequences to state outright:

- **A recursive field is not in scope in later field types.** It is not in
  the shape, so there is nothing for a later type to depend on. A field
  type that mentions a recursive field's name gets an unbound-name error.
  This is a real restriction (`Cons(t : Tree, p : t = t)` is unwritable) and
  it is the price of children-as-a-tuple: the tuple's element type is `⟦D⟧`
  uniformly, with no room for a per-position payload.
- **Distinct constructors can share a kernel shape summand.** `Tree`'s
  `Leaf` and `Node` both lower to `Σ(#tag). Unit⁰` — the *same* type. That
  is harmless and expected: the injection into the sum is what distinguishes
  them, exactly as it does for tier-0 `Bool`. The nominal tag still
  separates `Tree` from any structurally identical declaration.

## 3. The arity `n`

`n` is a `Nat` **term** with `x : S` free — a case on the tag returning each
constructor's literal recursive-field count:

```
Γ, x : S ⊢ n  :=  case x of { inl _ ⇒ m₁ | inr y ⇒ case y of { … } } : Nat
```

This is tier 0 §6.1's constant-motive case tree at the motive `Nat`, so it
is the *same* code again (`const_case_tree` with a new body kind), and it is
the one place where the shape's structure and the constructor list must
agree — they do because both come from `spine`.

Why a term and not a type: `Wf`'s arity contributes no level (§1.3 of the
former design), so `⟦D⟧` lives at the shape's level and nothing about the
recursion inflates the universe. It is also what would let a nested
declaration's arity be *data* (`snd x`) rather than a literal — the typing
half of §8.1, and the half that is genuinely free.

## 4. The type

```
⟦D<ā>⟧  =  Wf^l(x : S). n        at level l
```

Read back the other way: `tag_of` must see through a `Wf` to its shape, so
that a `Wf`-typed scrutinee still resolves to its declaration. This is the
one place where "the type determines the declaration" gains a case, and it
is checked by the same nominal-tag walk as tier 0's.

## 5. Constructors

```
⟦Cᵢ(ā)⟧  =  sup_f^l(x:S. n;  ℓᵢ(ā);  cs(ā))
```

where

- **`ℓᵢ(ā) : S`** — the *label*: tier 0 §4's injection-then-field-tuple,
  built by the same `build_ctor`/`build_fields` against `⟦Cᵢ⟧`, fed only the
  payload arguments.
- **`cs(ā) : Vec^l(⟦D⟧; mᵢ)`** — the *children*: the literal tuple
  `(r₁, (r₂, … (r_{mᵢ}, ⟨⟩)))` of the recursive arguments in declaration
  order, each checked at `⟦D⟧`.

The kernel's `sup_f` rule wants `cs : Vec^l(Wf; n[ℓᵢ/x])`, not
`Vec^l(Wf; mᵢ)`. Those are convertible and not equal: `n[ℓᵢ/x]` is a `Case`
on an `inl`/`inr`, which β-reduces to the literal `mᵢ`, and `Vec` reduces on
the *whnf* of its length. So the tuple is built at the literal and the
kernel's conversion closes the gap — the same discipline as tier 0's "the
annotations are read off the type being eliminated", one reduction later.

Annotation detail, and it is the kind that a test only catches at a nonzero
level: the tuple's `snd_ty` is the *tail* `Vec^l(⟦D⟧; k)` scoped **under**
the pair's first component, because `Vec(T; S k) ⇝ Σ(_ : T). Vec(T; k)` and
a `Σ`'s second component binds. So `snd_ty` is `⟦D⟧`'s tail shifted by one.
For a closed `⟦D⟧` (every monomorphic declaration today) the shift is
invisible, which is exactly why it is written down here.

## 6. `match`, and the recursor

The generated eliminator is one `elim_Wf` whose step **cases on the tag
first**, with `cs` and `ih` generalized in the case motive. That shape is
not a stylistic choice: outside a tag branch the arity `n[a/x]` is stuck on
a variable `a`, so `Vec` and `Fin` are neutral and neither the children
tuple nor the ih can be projected. Inside branch `i` the arity is the
literal `mᵢ`, `Vec` unfolds to a Σ-chain and `Fin` to a sum of `Unit`s, and
everything the user wrote becomes expressible. `crates/kernel/tests/wf.rs`'s
`mirror` is this shape, built by hand, and is the fixture the generator is
checked against.

### 6.1 The three types of the step telescope

Given the motive `M` over `(Γ, z : ⟦D⟧)` at level `l'`, the kernel's own
`term::wf_step_telescope(Γ, l, l', S, n, M)` returns

```
cs_ty    over (Γ, a)              =  Vec^l(⟦D⟧; n[a/x])
ih_ty    over (Γ, a, cs)          =  Π^{0,l'}(i : Fin n[a/x]). M[nth^l(⟦D⟧; n[a/x]; cs; i)/z]
step_ty  over (Γ, a, cs, ih)      =  M[sup_f(a; cs)/z]
```

The generator **calls it** rather than re-transcribing it. There are already
four verbatim copies of this telescope in the kernel (`typing.rs`, `conv.rs`,
`rec.rs`, `reduce.rs`) sharing one builder deliberately; a fifth copy in the
elaborator would be the drift the arrangement exists to prevent.

### 6.2 The step

Write `Γ₃ = (Γ, a : S, cs : cs_ty, ih : ih_ty)`. The step is

```
step  =  (P-case on a) cs ih                     : step_ty   over Γ₃
```

where the case's motive `P`, over `(Γ₃, z : S)`, is the telescope
re-abstracted at `z` in place of `a`:

```
P(z)  =  Π^{l,l'}(cs' : cs_ty[z]). Π^{l',l'}(ih' : ih_ty[z, cs']). step_ty[z, cs', ih']
```

and each branch of the case tree, at constructor `i` with binder
`c : ⟦Cᵢ⟧`, is

```
λ(cs' : cs_ty[inj_i c]). λ(ih' : ih_ty[inj_i c, cs']). ⟦armᵢ⟧
```

The two trailing applications are what re-connect the generalized `cs'`/`ih'`
to the real ones; their `cod` annotations bind their own argument and so sit
one level deeper than the ambient, which is the de Bruijn slip both kernel
acceptance tests made first (`issues/wf-former.md`, hazards).

The case tree itself is tier 0 §5.2's, unchanged in shape: right-nested
`Case`, the motive composed with `inl`/`inr` at each depth, no `Case` at all
at the last constructor.

### 6.3 What an arm binds

Inside branch `i`, with `c : ⟦Cᵢ⟧`, `cs' : Vec^l(⟦D⟧; mᵢ)` and
`ih' : Π(i : Fin mᵢ). M[nth …/z]`, the surface binders of `Cᵢ(b₁, …, b_k)`
are aliased — *not* kernel binders, as in tier 0 §5.1 — as follows:

| surface binder | lowering | type |
|---|---|---|
| payload field `j` | `fst (snd^{j+1} c)` — tier 0's projection | its declared type |
| recursive field, the `t`-th | `nth^l(⟦D⟧; mᵢ; cs'; ι_t)` | `⟦D⟧` |

where `ι_t : Fin mᵢ` is the literal index `inr^t (inl ⟨⟩)`, annotated with
`Fin` at each tail rather than its unfolded sum. At a literal `mᵢ` the `nth`
schema β-reduces to the projections of `cs'` even when `cs'` is a variable
(`wf.rs::nth_projects_out_of_a_neutral_tuple`), which is what makes an arm
binder behave like a field.

**Every binder is passed the literal `mᵢ`, never `n[inj_i c/x]`.** They are
convertible; the literal is the one that computes.

### 6.4 The induction hypothesis is a self-call

`issues/match-recursion.md`'s rule carries over exactly: a structurally
guarded self-call *is* the ih, and there is no `rec` keyword and no
fixpoint. What generalizes is the guard. For `Nat` a `Succ(k)` arm has one
descendant, `k`, and one ih. A `Wf` arm at constructor `i` has `mᵢ`
descendants, and the ih is a *function of the index*:

```
f(…, b_t, …)   ⇝   ih' ι_t        : M[⟦b_t⟧/z]
```

for `b_t` the `t`-th recursive binder — so the guard carries a table of
`(child term, ih application)` pairs instead of a pair of binder positions,
and the analysis matches the elaborated argument against the child terms.
Matching on the *term* rather than the name is what stops shadowing from
faking a guarded call, which is the same property the positional comparison
gave for `Nat`.

Everything else about the analysis is unchanged and stays untrusted: the
call must be saturated, must descend in the parameter the `match` scrutinizes,
must pass every other parameter unchanged, and can only ever be *rejected* —
whatever it lets through is still an `elim_Wf` the kernel re-checks.

The ih is transient in exactly the sense of the former design §4: it is
applied at literal indices inside the arm and never stored, compared, or
returned. Nothing in the generated term needs it to be η-expandable, which
is why no funext obligation appears anywhere in this scheme.

**How the ih is spelled after a step fires.** The kernel's ι-rule writes the
ih as `λ i. elim_Wf(…; step; nth(cs; i))`, so every arm the β exposes
carries a copy of the whole step: the case tree over *all* constructors.
Over an `n`-constructor type, a lemma whose motive mentions another
recursion over the scrutinee (`t.lift(k, u) = t`) then paid work linear in
`n` per arm, quadratic over the lemma
(`issues/wide-inductive-lemma-quadratic-gate.md`). Two places now keep the
ih as what it came from:

- The elaborator *refolds* it (`crates/elab/src/refold.rs`): when a step
  that fires is the stored body of a defined global `g` whose layout is
  `λ x̄. elim_Wf(…; x_s) x̄_varied`, the ih is spelled `λ i. λ q̄. g(…,
  nth(cs; i), …, q̄)`, a call, in both the small-step reducer the unifier
  walks and the value machine's readback. The two are definitionally equal
  (δ then β), so nothing the kernel checks changes; what changes is that
  solved implicits and read-back types stay the size of the source.
- The kernel's value machine applies a held ih at a neutral child by
  evaluating only the `nth` and eliminating it with the *same* `elim`
  (`Eval::wf_ih_child`), instead of building a λ around a shifted copy of
  the step. Two recursive calls on one neutral child, one through the ih and
  one through the definition, then share the step's closure, and conversion
  answers them by identity rather than by comparing case trees.

The unifier's own head walk still descends the case tree one constructor at
a time by substitution, which is the remaining superlinear term
(`issues/wide-inductive-unifier-case-descent.md`).

## 7. No-confusion

Both halves are tier 0 §6's, with `Case`-on-the-scrutinee replaced by
`elim_Wf`-with-a-constant-motive-and-a-`Case`-on-the-tag. In each, the step
ignores `ih` entirely — no-confusion is not an inductive argument.

*Correction, made while writing the code.* That is true of everything except
**injectivity at a recursive field**, and the first draft of §7.2 below had it
wrong. A constant motive frees the step from `ih`; it does *not* free it from
`cs`. Reading the `t`-th child means `nth^l(⟦D⟧; mᵢ; cs; ι_t)` at the
**literal** `mᵢ`, and outside a tag branch `cs : Vec^l(⟦D⟧; n[a/x])` is stuck
on the variable `a` — so `Vec^l(⟦D⟧; mᵢ)` is not convertible with it and the
projection does not typecheck. That case therefore needs §6.2's
generalization, exactly as `match` does, and shares the code that does it
(`wf.rs::build_elim_wf`, over a `Branches` choice of branch body); only the
two `ih`-free cases go through the simpler `const_elim_wf`. The kernel caught
this as a `NotConvertible`, which is the cheap half of the hazard class — the
expensive half is the bug that typechecks.

- **§7.1 Disjointness (`absurd`).** The tag predicate
  `tagᵢ : ⟦D⟧ → Ty 0` is `elim_Wf` at motive `Ty 0` (motive level 1) whose
  step is the constant case tree returning `⌜Unit⁰⌝` at `i` and `⌜Empty⁰⌝`
  elsewhere. Then the `J` motive is `El⁰(tagᵢ y)`, the `refl` case is `⟨⟩`
  because `El⁰(tagᵢ lhs) ⇝ Unit⁰` definitionally, and the transported term
  inhabits `Empty⁰`. Large elimination over a `Wf` needs no new kernel
  power: `elim_Wf`'s motive is an arbitrary `Type`, so it may be `Ty 0`,
  exactly as `Case`'s may.
- **§7.2 Injectivity (`inj`).** The `k`-th field projection is `elim_Wf` at
  the *constant* motive "that field's type", whose step is the case tree
  returning
  - `fst (snd^{j+1} a)` for a payload field `j` — that field's index among
    the payload, which is not its index among the surface fields, and
  - `nth^l(⟦D⟧; mᵢ; cs; ι_t)` for the `t`-th recursive field, **through
    §6.2's `cs` generalization** (see the correction above); its motive is
    `⟦D⟧` itself, and there is nothing for it to depend on,

  and, at every other constructor, the left-hand side's own field value —
  the same totality trick as tier 0 §6.2, and the same restriction it
  carries for payload fields (the field's type must not depend on an earlier
  field, checked by conversion rather than assumed).

Reading a constructor term back (`read_ctor`, which is what decides *which*
constructor each side of the equation is) gains a `Supf` case: walk the
label's injections for the index, then take the payload values from the
label's Σ spine and the recursive values from the children tuple, and
re-interleave them into declaration order.

Inside an eliminator arm the label and children may be neutral. Disjointness
needs only the label's injection path and deliberately does not decode the
children vector; this is what lets `absurd` consume an equation between the
arm's own scrutinee and a different constructor. Injectivity still requires
the field values it returns.

## 8. Not covered here

- **Indexed families** still ford by `Id`, tracked separately.
- **Infinitary branching** stays on `W`: its positions are a *type*, not a
  `Nat`. Since 2026-10-20 it is lowered, not merely classified, for a
  recursive function field (`k: A -> D`) with at most one recursive field per
  constructor: `docs/inductive-tier2-w-lowering.md`. It needs no funext
  axiom; a leaf predicate carried beside the tree stands in for the
  `Empty`-domain η the kernel lacks (that document's §2).
- **Mutual** declarations: no scheme yet at any tier.
- **Polymorphic containers.** The level constraint is gone (route (a) of
  `unit-empty-level-indexing.md`) and the kernel side is exercised by
  `wf.rs::polymorphic_shape`, but nothing at the *surface* can reach it: a
  tier-0 type parameter is monomorphized, and the surface's type grammar
  (`Nat`, a named declaration, `=`) has no inhabitant above level 0 to
  instantiate one with. Nothing here assumes level 0 — the level is taken
  from the shape throughout — so this is a surface gap, not a lowering one.

### 8.1 Nested recursion, and why it is not one step away

`wf-former-design.md` §7 records `Rose { Node(A, List Rose) }` as "nearly
free", on the grounds that `S = Σ(a : A). Nat` and `n = snd x` type it: the
child list *is* the `Vec` and its length is data in the shape. That is true
of the **type**, and it is the reason arity-as-a-term was worth having. It is
*not* true of the lowering from a surface declaration whose field type is a
user-declared `List`, and the difference is worth stating precisely, because
"nearly free" would otherwise be read as "a small round".

The obstruction is that the generator would have to identify the user's
`List<Rose>` with the kernel's `Vec^l(⟦Rose⟧; k)`. Both directions are
*definable* — `Vec → List` by `elim_Nat` on the length, `List → Σ(n : Nat).
Vec` by `elim_Wf` on the list — so this is not a typing problem. It is a
**computation** problem:

- `Node(xs)` for a *neutral* `xs` lowers to `sup_f(⟨a, len xs⟩; toVec xs)`,
- and `match Node(xs) { Node(ys) ⇒ ys }` gives back `fromVec (toVec xs)`,
- which is convertible with `xs` only for a canonical `xs`.

So β would stop firing on open subterms — precisely the property that
distinguishes this tier from every finitary encoding, and the property route
C was chosen for (`branching-inductives-choice.md` §15). A lowering that
loses it is not the tier.

What actually unblocks it is **surface support for a children-container field
type** — a field the declaration states *as* a vector of `D`, so that the
container in the source and the `Vec` in the kernel are the same object and
no conversion appears. That is a surface-language round (a new `TyKind`, its
elimination forms, and what a `match` arm binds for it), not a generator
tweak.

**Done, phase 1, 2026-07-26: `docs/container-fields.md`.** `Rose` is written
`Node(label: Nat, len: Nat, kids: [Rose; len])` — the length is an ordinary
payload field and `[Rose; len]` is the kernel's `Vec` directly, so the arity
term projects `len` out of the shape and the children tuple's tail *is* the
container. A *nested* occurrence (`List Rose`) is still rejected with the
message below, and correctly: this closes the gap by adding the container to
the surface, not by identifying a user declaration with `Vec`.
- **Indexed families** still ford by `Id`, tracked separately.
- **Infinitary branching** stays on `W`: its positions are a *type*, not a
  `Nat`. Since 2026-10-20 it is lowered, not merely classified, for a
  recursive function field (`k: A -> D`) with at most one recursive field per
  constructor: `docs/inductive-tier2-w-lowering.md`. It needs no funext
  axiom; a leaf predicate carried beside the tree stands in for the
  `Empty`-domain η the kernel lacks (that document's §2).
- **Mutual** declarations: no scheme yet at any tier.

## 9. What retires, and what does not

`docs/inductive-tier1-lowering.md`'s exact-height fording scheme is **not
the generator's path**: `List`/`Bits` fold into this one as arity-≤1
declarations, and the height machinery is not used by any lowering. It stays
as the costed record of a scheme that was designed, prototyped and not
taken, alongside `crates/elab/tests/branching_route_a.rs`; its prototype
`crates/elab/tests/tier1_fording.rs` stays live as a *kernel stress suite*,
and its `vec` formula survives as `Type::Vec`'s reduction semantics.

## 10. Acceptance checklist

**All eight met**, 2026-07-26, in `crates/elab/tests/inductive_tier1.rs` (13
tests). Every item below names the test that pins it.

1. `Tree { Leaf, Node(Tree, Tree) }` declares, and `⟦Tree⟧` kernel-checks as
   a `Wf` — `tree_declares_and_builds`.
2. `Leaf` and `Node(l, r)` check at `⟦Tree⟧`, including at *open* children —
   same test, and `beta_fires_on_open_children` for the reduction that needs
   it.
3. `mirror` elaborates from a surface `match` with self-calls, and closed
   trees compute — `mirror_computes`, three `refl`s.
4. **`mirror(mirror(t)) = t`** by a surface recursive `theorem`, matching by
   hand what `crates/kernel/tests/wf.rs` does — `mirror_of_mirror`. This is
   the acceptance in `issues/tier1-branching-constructors.md`.
5. Arities 0/1/2 in one declaration, with payload fields alongside recursive
   ones, and `match` β-firing on each — `mixed_arities_and_payloads`; and
   `each_child_has_its_own_ih`, where an *asymmetric* motive is what would
   catch a swapped `Fin` index.
6. A linear declaration lowers through the same path —
   `linear_declarations_fold_in`. The tier folds in rather than sitting
   beside; the fording scheme is unused by any lowering (§9).
7. No-confusion: `absurd` between two constructors, and `inj` at a payload
   field and at a recursive one — `no_confusion`,
   `injectivity_across_payload_and_children`.
8. Rejections stay rejections — `nested_recursion_is_diagnosed`,
   `a_recursive_field_is_not_in_scope_later`, `a_self_call_must_descend`,
   `a_self_call_outside_a_match_is_rejected`, and tier 0's
   `a_recursive_declaration_is_classified_not_lowered`, which now pins the
   *boundary* (direct occurrences lower, nested ones do not) rather than a
   blanket refusal.
