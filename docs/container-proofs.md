# Container fields phase 3: proofs by induction over a container

Status: **implemented 2026-07-26.** `crates/elab/tests/container_proofs.rs` is
§8's checklist (4 tests), plus 3 kernel-level ones on the schema in
`crates/elab/src/vec.rs`; workspace at 421. §10 records what implementing
found — including two live shift bugs, one of them pre-existing and neither
visible to any phase-2 test. This was the design round
`docs/container-fields.md` §4.3 declines to do inline, per the discipline of
`docs/inductive-tier0-lowering.md` and `docs/inductive-tier1-wf-lowering.md`:
the scheme is written, and its acceptance checklist is fixed, before any code.
Tracking issue: `issues/nested-inductives-container-fields.md`.

Phase 1 made `Rose` declarable and matchable, phase 2 made it *programmable*
(`kids.map(size).fold(…)`). What is still rejected — with a message naming
§4.3, `crates/elab/tests/container_recursion.rs::rejections` — is a **theorem**
proved by induction into the children.

---

## 1. What exactly is missing

A `Wf` arm receives

```
ih' : Π(i : Fin (Succ^m len)). M[nth cs i / z]
```

— `m` plain children first, then the container's (`docs/container-fields.md`
§10.3). Phase 2 turns that into data with `tabulate`, whose result is a
`Vec^l(B; len)`, and a `Vec` has **one element type**. So phase 2 must
strengthen `M` out of `z` (`vec::strengthen`), and refuses when it cannot:

```heather
theorem refl_all(r: Rose): r = r {
    match r { Node(label, len, kids) => kids.map(refl_all) }   // rejected today
}
```

A dependent `M` is exactly the proof case: the ih at index `i` proves
something *about* `kids[i]`, so the `n` results do not share a type and there
is no vector to tabulate into. That is the whole of the problem, and it is the
classic nested-induction one.

## 2. The target, stated as a program

Phase 2's acceptance was `size`. Phase 3's is the smallest theorem that
genuinely needs the children's ih — two container recursions that agree at
every node, so nothing but the ih can relate them:

```heather
inductive Rose { Node(label: Nat, len: Nat, kids: [Rose; len]) }

fn add(a: Nat, b: Nat) -> Nat { match b { Zero => a, Succ(k) => Succ(add(a, k)) } }

fn size(r: Rose) -> Nat {
    match r {
        Node(l, n, kids) => Succ(kids.map(size).fold(0, λ (a: Nat) (b: Nat) => add(a, b))),
    }
}

fn size_plus(r: Rose) -> Nat {
    match r {
        Node(l, n, kids) =>
            add(kids.map(size_plus).fold(0, λ (a: Nat) (b: Nat) => add(a, b)), 1),
    }
}

theorem same(r: Rose): size(r) = size_plus(r) {
    match r {
        Node(l, n, kids) => cong_succ(cong_fold(n, kids.cong(same))),
    }
}
```

Two things about this example are deliberate.

- `add(x, 1) ⇝ Succ x` **definitionally** (`add` recurses on its second
  argument), so the node-local step needs no arithmetic lemma. The *only*
  gap between the two sides is the two vectors of children results, which is
  the gap phase 3 exists to close. A target needing `add`-commutativity would
  have tested Nat lemmas instead of this round's machinery.
- `cong_fold` is written by hand, monomorphically, exactly as
  `crates/elab/tests/tier1_list_proofs.rs` writes `cong_cons`:

```heather
theorem cong_fold(n: Nat, {xs: [Nat; n]}, {ys: [Nat; n]}, p: xs = ys):
    xs.fold(0, λ (a: Nat) (b: Nat) => add(a, b))
        = ys.fold(0, λ (a: Nat) (b: Nat) => add(a, b))
{ j(p, (y, q) -> xs.fold(0, λ (a: Nat) (b: Nat) => add(a, b))
                     = y.fold(0, λ (a: Nat) (b: Nat) => add(a, b)), refl) }
```

That is an ordinary `j`, needs nothing new, and is the standing tax of having
no polymorphism below layer m. Phase 3 does **not** try to remove it.

## 3. The fork, and why it goes the way it does

§4.3 named two honest options. Both are *available*; they are not equally
*usable*, and that is the decision.

### 3.1 Route A — an `All` predicate over a vector

Define, by recursion on the length,

```
All^l(P; 0;   xs) = Unit
All^l(P; S k; xs) = Σ(_ : P (fst xs)). All^l(P; k; snd xs)
```

and give the arm a binder of that type: a Σ-chain of the `n` sub-proofs.

This **is** definable in the kernel, and it is worth being precise about that
rather than waving it off. It needs large elimination — an `elim_Nat` whose
motive is `Ty l` — which exists: codes are terms (`Term::TmSigma`,
`Term::TmUnit`, …), `Type::El` decodes them, `El` of a stuck code steps the
code (`crates/kernel/src/reduce.rs:134`), and code formation is barred only at
`Layer::Var` (`typing.rs::not_var_layer`), not at `Prog`. So route A is not
blocked by the kernel.

It is blocked by the **surface**. `All(M; kids)` is evidence, and consuming it
means an induction on the length, which the surface cannot write: there is no
recursion on a `Nat` that is not a `match` on a declared inductive, no `Fin`
type and no `xs[i]` (`docs/container-fields.md` §7), no polymorphism, and no
way to state a type-valued motive over a vector at layer 0. Route A therefore
hands the user a value **no surface program can eliminate**, and every actual
use would have to be a further built-in schema anyway.

Producing unusable evidence is worse than producing none: it makes the feature
look present in the tests while every real proof still dead-ends.

### 3.2 Route B — the pointwise vector congruence (chosen)

Keep the ih pointwise, and close the *goal* instead of exposing the evidence.
In every proof of the §2 shape the motive is an equation

```
M(z) ≡ Id^l(A; lhs(z); rhs(z))          with A independent of z
```

and what the goal needs is precisely that the two **vectors** of results are
equal:

```
tabulate(len; λi. lhs(kids[i]))  =  tabulate(len; λi. rhs(kids[i]))
```

which is exactly `kids.map(lhs) = kids.map(rhs)` — the two terms phase 2
already builds, one on each side of an `Id`. So phase 3 is one new schema in
`crates/elab/src/vec.rs`, alongside `map`/`fold`/`tabulate`, plus a typing rule
for the self-call at an `Id` motive. **No new kernel machinery, no `All`, no
funext, no large elimination.**

The cost, stated plainly: route B closes goals whose motive is an `Id`, and
nothing else. A motive that is an inductive predicate (`Sorted`, `Elem`) is
still rejected, and route A remains its future — at which point it will also
need the surface indexing layer, and should be done *with* it. §7 records that.

## 4. The schema

```
tab_cong^l(A; n; f; g; h) : Id^l(Vec^l(A; n); tabulate(A; n; f); tabulate(A; n; g))
    for  f, g : Π(i : Fin n). A
         h    : Π(i : Fin n). Id^l(A; f i; g i)
```

An `elim_Nat` on the length, like every other schema in that module — the
length is the only thing a vector reduces on. Motive in `(Γ, k̂)`:

```
Π(f : Π(i : Fin k̂). A). Π(g : Π(i : Fin k̂). A).
    (Π(i : Fin k̂). Id(A; f i; g i)) → Id(Vec(A; k̂); tabulate(k̂; f); tabulate(k̂; g))
```

**Base (`k̂ = 0`).** `tabulate(0; f) ⇝ ⟨⟩` on both sides, and the type
`Vec(A; 0) ⇝ Unit^l`, so the two sides are convertible by `Unit`-η
(`conv.rs:789`, proof irrelevance, type-directed) and the base is `refl`.
Note what carries this: conversion dispatches on the *reduced* type, so
`Vec(A; 0)` must reduce to `Unit` before the η arm is reached — the same fact
`docs/wf-former-design.md` §9.4 leans on for the nullary constructor.

**Step (`k̂ ↦ S k̂`).** `tabulate(S k̂; f) ⇝ (f ι₀, tabulate(k̂; λj. f (inr j)))`
— it reduces at a *neutral* `k̂` because the scrutinee is `Succ`-headed, which
is the same load-bearing fact as `docs/container-fields.md` §3.3 — and
`Vec(A; S k̂) ⇝ Σ(_ : A). Vec(A; k̂)`, a **non-dependent** Σ. So the step is a
congruence of pairing in two arguments, built from two `J`s and no `trans`:

```
p  = h ι₀                                   : Id(A; f ι₀; g ι₀)
q  = r (λj. f (inr j)) (λj. g (inr j)) (λj. h (inr j))
                                            : Id(Vec(A; k̂); tab_f; tab_g)
e₁ = J(q, (y, _) ↦ Id(Vec(A; S k̂); (f ι₀, tab_f); (f ι₀, y)), refl)
e₂ = J(p, (y, _) ↦ Id(Vec(A; S k̂); (f ι₀, tab_f); (y,    tab_g)), e₁)
```

`e₂` is the step's result. Each `J` moves one component; the second's `case`
is the first's result, which is why no transitivity lemma is needed. `A` is
independent of the index throughout, so no motive here is dependent and no
transport appears.

## 5. The typing rule at the surface

`ContainerIh` (`crates/elab/src/lib.rs`) currently carries
`result: Option<Type>` — the strengthened motive, `None` when it depends,
which is today's rejection. Phase 3 adds a second, mutually exclusive field,
computed in `wf::wf_branch` where the motive is in scope over `(Γ₀, z)`:

```rust
/// The motive read as an equation, when it is one: `M(z) ≡ Id^l(A; lhs; rhs)`
/// with `A` independent of `z`. `lhs`/`rhs` are scoped over `(Γ₀, z)`.
eq: Option<EqSplit { level: Level, ty: Type, lhs: Rc<Term>, rhs: Rc<Term> }>,
```

obtained by whnf-ing the motive, matching `Type::Id`, and `vec::strengthen`-ing
its `ty` (`Id`'s endpoints may mention `z` freely; only its *type* may not).

At the call site (`elab_container_ih`), when `result` is `None` and `eq` is
`Some`, build — with `kids` the container binder term and `m` the plain-child
count, both already there:

```
f' = λ(i : Fin len). lhs[nth(kids; i) / z]
g' = λ(i : Fin len). rhs[nth(kids; i) / z]
h  = λ(i : Fin len). ih (inr^m i)          -- verbatim phase 2's index map
```

and emit `tab_cong(l; A; len; f'; g'; h)` at type
`Id(Vec(A; len); tabulate(len; f'); tabulate(len; g'))`.

Three things to notice, each of which is why this is small:

- **`h` is the term phase 2 already builds.** `elab_container_ih` constructs
  `λ(i : Fin len). ih (inr^m i)` today and hands it to `tabulate`; phase 3
  hands the same λ to `tab_cong`. Its type is `Id(A; lhs[kids[i]]; rhs[kids[i]])`,
  which is `Id(A; f' i; g' i)` up to β. The `m` `inr`s — the offset a mixed
  constructor forces (`docs/container-fields.md` §10.3) — are therefore
  exercised by phase 3 for free, and must be tested asymmetrically for the
  same reason.
- **The result's endpoints must be convertible with the goal's.** After the
  `Wf` β at a constructor form the goal side contains
  `tabulate(len; λi. elim(nth(cs; inr^m i)))` (`reduce.rs:374` builds the ih as
  `λi. elim_Wf(… nth(children; i))`), and `nth(cs; inr^m i) ⇝ nth(snd^m cs; i)`
  because the arity is `Succ`-headed exactly `m` times. This is the one claim
  in this document that neither the schema's own test nor the type checker can
  establish on its own, and §8 makes it a checklist item rather than an
  assumption.
- **No new rejection path.** The existing message stays, for the case where the
  motive is dependent *and* not an equation; it just stops firing on the case
  phase 3 handles.

## 6. Spelling

The receiver is a vector, the argument is the self-name, and the **result is a
proof** — not a vector. So phase 2's `kids.map(self)` is the wrong word here:
`map` returns data everywhere else in the surface.

Proposed: **`kids.cong(self)`**. It reads as what it is — the congruence of the
children map under the ih — and it matches the existing `.cong(f)` on a proof
(`issues/surface-operators.md`, discharged by
`docs/constructor-function-values.md`), which is the same idea one arity down. The two
are distinguished by receiver type (vector vs `Id`), the way `map`/`fold`
already are, and both are recognized syntactically rather than resolved as
values, since the self-name is not a value (`issues/match-recursion.md`).

Rejected alternatives: `kids.map(self)` at an `Id` motive (overloads `map`'s
result kind — data in one context, a proof in another, decided by a motive the
reader cannot see at the call site); `kids.map_cong(self)` (accurate, but names
an implementation schema in the surface language).

## 7. Not in phase 3

- **A non-`Id` motive** — an inductive predicate over `Rose`. Route A (§3.1) is
  its answer, and it should land *with* the surface indexing layer (`Fin`,
  `xs[i]`), not before: without a way to eliminate a vector, `All` is
  unusable evidence.
- **A heterogeneous motive** — `Id` whose *type* mentions `z`. That is the same
  transport question as `issues/dependent-field-injectivity.md`, which already
  holds two instances of it (a dependent payload field, and `inj` at a
  container field). It should be lifted once, there, for all three.
- **`mirror(mirror(t)) = t`**, §4.3's own example. It needs a vector `reverse`,
  and `reverse` is a fourth `elim_Nat` schema that nothing else wants yet; the
  theorem then needs `reverse`-involutivity, which is a lemma about the schema
  rather than about `Rose`. Out of scope, and the issue should stop quoting it
  as the phase-3 target — §2's `same` is the honest one.
- **Removing the hand-written `cong_fold`.** Polymorphic congruence is layer-m
  work (`issues/elab-unifier-completeness.md`, universe polymorphism), and this
  round pays the same tax `tier1_list_proofs.rs` pays.
- **Two containers, or a plain child after one** — unchanged phase-1
  restrictions.

## 8. Acceptance checklist

1. **`tab_cong` is kernel-tested before any surface syntax reaches it**, in
   `vec.rs`'s test module, at a literal length *and* at a neutral one — the
   direct lesson of §10.1, where both `map` and `fold` had the step's domain
   off by a `Succ` and it cost seconds instead of an opaque `NotConvertible`
   three layers up.
2. At a literal length, `tab_cong` applied to a pointwise `refl` is convertible
   with `refl` — the schema computes, not merely types.
3. §2's `same` elaborates and kernel-checks. This is the acceptance: it is the
   first theorem in the codebase proved *by induction over a container*.
4. The mixed case: the same theorem over a constructor with a plain child
   **and** a container, with an **asymmetric** tree, so an off-by-one in the
   `inr^m` offset cannot pass (`§10.3`'s reason).
5. **The negative control**, and it is the one that matters — the §9.1 lesson
   is that positive tests cannot distinguish a type from a quotient of it. A
   *false* theorem of the same shape (`size(r) = Succ(size_plus(r))`, discharged
   the same way) must be rejected by the kernel, not accepted.
6. A container proof whose motive's `Id` *type* depends on `z` is rejected with
   the heterogeneous message pointing at
   `issues/dependent-field-injectivity.md`, not mis-lowered.
7. A non-`Id` dependent motive keeps today's §4.3 message, and the message is
   updated to say that the *equation* case now works.
8. Phases 1 and 2 are unchanged: the whole existing suite passes, and
   `refl_all`'s rejection in `container_recursion.rs::rejections` is replaced
   by a case that states what is now supported.

## 9. Risk (resolved — see §10.3)

One claim carries this design: that the `tab_cong` endpoints
(`tabulate(len; λi. lhs(kids[i]))`) are convertible with what the goal contains
after the `Wf` β (§5, second bullet). Everything else is checked by the kernel
the moment it is built. If that conversion does not fire, the fallback is not
route A — it is to make the *lifting* produce the goal's own spelling by
reusing `elab_container_ih`'s existing term for each side, which is a change of
two lines in what `f'` and `g'` are, not a change of design. Checklist item 3
is what discovers this, and it should be attempted **immediately after** item 1
rather than at the end of the round.

---

## 10. What implementing phase 3 found

### 10.1 `tabulate`'s index-function type had a live shift bug

`vec::tabulate`'s `idx_fun` built `Π(i : Fin k). B` with `B` shifted by the
*ambient* depth. `B` sits under the `Fin` binder, so it needed one more. The
schema has been wrong since phase 2 landed, and **every existing test passed**:
`map`, `fold` and `tabulate` were only ever exercised at `B = Nat`, which is
closed, and a wrong shift on a closed type is the identity.

`tabulate_at_an_open_element_type` is the control that fails without the fix —
an element type `Vec(Nat; m)` mentioning an ambient variable, which is what any
container recursion at a non-closed result type produces. The same control was
then written for `map` and `fold` (both were correct), so the audit covers the
module rather than the one schema that failed it.

This is the same lesson as §10.1 of `container-fields.md`, one level up: a
schema wants a test at the level it is generated, *and* at a general enough
instance. Closed types are to shifts what positive tests are to quotients.

### 10.2 A plain child's ih was broken inside a container constructor

Pre-existing, and phase 3 is only what exposed it. In `wf::wf_branch` the
codomain annotation for a plain child's ih is `M[nth(…; len; cs; i)/z]`, built
one binder deeper than the arm — and everything in it was shifted except the
**length**. Without a container the length is a closed literal, so the missing
shift is invisible; with one it is `Succ^m(projection out of the label)`, which
mentions variables, and the annotation is wrong.

Why phase 2 could not see it: phase 2's mixed-constructor test
(`a_plain_child_and_a_container_recurse_together`) only *computes*, on closed
values, where the elim β-reduces and the annotation is never compared. It takes
a **proof** — where the ih's stated type has to convert with the goal — to
notice. `container_proofs::a_plain_child_and_a_container_prove_together` is that
test, and it fails without the fix.

It is a completeness bug, not a soundness one: the wrong annotation makes the
kernel reject a valid proof rather than accept an invalid one.

### 10.3 The conversion §9 flagged as the risk fired on the first try

The acceptance theorem checked as soon as the plumbing compiled, which settles
the one claim the design could not establish on paper: `tabulate(len; λi.
lhs(kids[i]))` *is* convertible with what the goal holds after the `Wf` β,
because `nth(cs; inr^m i) ⇝ nth(snd^m cs; i)` at a `Succ`-headed arity. No
fallback was needed.

### 10.4 The boundary is the equation's *type*, not the goal

`theorem rr(r: Rose): r = r` looks like the case phase 3 excludes, and it is
not: `Rose` does not mention the scrutinee, so the lifting is built — it proves
the two children vectors equal, which is simply not that goal, and the kernel
says so. The genuinely out-of-scope case needs an `Id` whose *type* mentions
`z`, which the surface can now write (`xs : [Nat; size(r)]`) and which is
diagnosed. Both are tested, because the pair is what pins where the line is.

### 10.5 `.cong` needed no name reservation

The dispatch fires on the *self-name argument*, not on the name `cong`, so a
user-defined `cong` theorem — which `constructor_values.rs` has — still
resolves for the ordinary `p.cong(f)`. Nothing had to be shadowed or renamed,
and the reason is the same one that makes the whole lifting syntactic: the
self-name is not a value, so it can never be an argument to a real function.
