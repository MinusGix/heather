# Extending DeLaM: declarative rules for six type formers

*Companion to DeLaM ch. 04 (`docs/delam/04_dependent_layered_modal_type_theory.tex`).
This document is standalone: it restates enough of the ambient system to be read
on its own, and is written so that its rules can be transcribed into a proof
assistant without further consultation.*

---

## 0. What this document is, and who it is for

DeLaM — **De**pendent **La**yered **M**odal type theory — is a dependently typed
metaprogramming calculus. Its distinguishing feature is a *recursive elimination
principle for code*: a program can take a piece of syntax, split it into cases by
which former it is, and recurse into its sub-structures, all while the kernel
guarantees that the syntax it is handed is well typed. Chapter 04 of the DeLaM
development gives the declarative type theory: judgments, typing rules,
equivalence rules, computation rules. Chapter 06 gives the *algorithm* — untyped
weak-head reduction plus algorithmic convertibility — and chapters 07/08 relate
the two by instantiating a generic Kripke logical relation twice, once at each,
which is what yields soundness *and* completeness of the checker against a
specification.

Chapter 04's MLTT fragment is deliberately minimal: `Nat`, `Π`, a Tarski-style
universe hierarchy `Ty l`, and universe-polymorphic functions `ΠΠ`. It has no
`Id`, no `Σ`, no `Unit`, no `Empty`, no `+`, no `W`. The Heather kernel adds all
six and implements them. Their declarative rules — the ch. 04-style judgments, as
opposed to the algorithm — have until now existed only implicitly, in the
checker's source and in our heads. That is an uncomfortable place for them to
live: it means we have been claiming that our conversion checker is sound and
complete with respect to a specification we never wrote down. This document is
that specification.

**Three consumers shape how it is written.**

1. *A paper or blog post of our own.* Hence the self-contained framing, the
   paper's notation and rule style, and the prose explaining why each addition
   is shaped the way it is.

2. *A Coq formalization.* The author of this repository is independently
   formalizing DeLaM-with-our-alterations in Coq, and this document is the
   natural input to extending it. Consequently there is **no "as usual" and no
   elided premise** anywhere below. Every telescope is spelled out entry by
   entry. Every universe-level side condition is written, including the ones a
   human reader would supply automatically (`⊢_L l : Level` on every level a
   rule mentions; `⊢_L l ≈ l' : Level` wherever two annotations are compared).
   Every substitution is written with its domain explicit. Where a rule's
   conclusion mentions a context extension, the extension's level annotation is
   given. This makes the rules verbose; that is the point.

3. *Ourselves, six months from now, deciding where the checker and the spec are
   allowed to disagree.* §16 is a candid list of the places where the
   implementation makes a choice that a declarative specification should *not*
   fix, plus the places where they currently disagree and one of them is wrong.
   That section is, in a real sense, the return on writing this document at all.

**What is in scope.** The six formers named above: for each, formation,
introduction, elimination, β, η where it exists, the term-level *encoding* and
its decoding rule, the congruence rules, and the code-recursor branches (the
`G_A` telescope). Plus §14, the definitions extension (bodied global bindings and
δ), which is a binding form rather than a type former but belongs to the same
ledger.

**What is out of scope**, and deliberately so, is listed in §17: the kernel also
has `sEq`/`sEmpty` (strict, definitionally proof-irrelevant equality), and
`Vec`/`Fin`/`Wf` (the finitary branching substrate). Those arrived in later
rounds with their own design documents; folding them in here would double the
length without exercising a new idea, and the marginal cost of adding them later
is exactly what writing the six down properly buys.

**What is also out of scope**: the ch. 06 side. This document says nothing about
the weak-head-normal grammar, the neutral grammar, or algorithmic convertibility
for the new formers. Those exist in the kernel (`reduce.rs`, `conv.rs`) and are
argued in `docs/metatheory-ch07-extensions.md`; §16 notes where they and the
declarative rules could come apart, but transcribing them is a separate job.

---

## 1. DeLaM in one page

Enough of the ambient system to read the rules. All of this is ch. 04; nothing
here is ours.

### 1.1 Layers

There are four layers, ordered `v < c < p < m`:

| layer | language | computes | meta-programs | layer of its types |
|-------|----------|----------|---------------|--------------------|
| `v` | variables only | no | no | `p` |
| `c` (code) | MLTT | **no** | no | `p` |
| `p` (prog) | MLTT | yes | no | `p` |
| `m` (meta) | MLTT + `□` + recursors + `ΠΠ` | yes | yes | `m` |

Every judgment carries a layer index `i`. Layer `c` is where *static code* lives:
at `c` nothing computes, so two pieces of code are equal only when they are
syntactically equal, which is exactly the equality the code recursor dispatches
on. Layer `p` exists because dependent types force *code promotion*: the type of
a piece of code may itself contain computation (if `f : Π(x : Ty 0). x` then
`box (f ((λx.x) Nat))` has type `□(Δ ⊢ (λx.x) Nat)`, which we want to be
`□(Δ ⊢ Nat)`), so types must compute even when the term they classify does not.
The function

```
typeof(v) = typeof(c) = typeof(p) = p          typeof(m) = m
```

says which layer a term's *type* lives at, and

```
⊨ p comp        ⊨ m comp
```

marks the computing layers. **All β and η rules are stated under `⊨ i comp`.**
That guard is not decoration; §11.3 and §14.2 both turn on it.

### 1.2 Universe levels

Levels `l ::= ℓ | 0 | 1 + l | l ⊔ l' | ω` form an idempotent commutative monoid
under `⊔` with unit `0`, with `1 + −` distributing over `⊔` and absorbing
(`l ⊔ (1 + l) ≈ 1 + l`). Level equivalence `⊢_L l ≈ l' : Level` is decidable and
is settled by the `adjust ∘ count` normalization of ch. 04 §Universe Levels. The
level `ω` is not well-formed (`⊢_L ω : Level` does not hold); it arises only as
the level of `ΠΠ` and `Λ ℓ⃗`, and appears in no rule below.

Universes are **non-cumulative**: every type has exactly one level, and levels are
compared by `≈`, never by `≤`. This is load-bearing rather than tidy — the code
eliminator must reconstruct code from its components in each branch, which is
only expressible when each term has a unique type. It is why `Unit` and `Empty`
below are level-*indexed* (§7.0) rather than level-polymorphic, and why the
levels on `elim_Empty` are two independent annotations rather than one.

### 1.3 Contexts and judgments

Three context kinds: a universe context `L` of level variables `ℓ`, a global
context `Ψ` of code bindings, and a local context `Γ` of ordinary variables.

```
Γ, Δ  ::=  ·  |  g  |  Γ, x : T @ l
B     ::=  g : Ctx  |  U : Typ_i(Δ, l)  |  u : Trm_i(Δ ⊢ T @ l)
Ψ, Φ  ::=  ·  |  Ψ, B
```

with `i ∈ {c, p}` for `Typ` bindings and `i ∈ {v, c}` for `Trm` bindings. A local
context may be *based* at a context variable `g`, which is what lets the code
recursor quantify over the context a piece of code lives in.

The judgments used below, all implicitly under an ambient `L`:

```
⊢_L Ψ                       Ψ well formed
Ψ ⊢_i Γ                     Γ well formed at layer i
Ψ ⊢_i Γ ≈ Δ                 local contexts equivalent
Ψ; Γ ⊢_i T @ l              T is a type at level l
Ψ; Γ ⊢_i t : T @ l          t inhabits T at level l
Ψ; Γ ⊢_i T ≈ T' @ l         type equivalence
Ψ; Γ ⊢_i t ≈ t' : T @ l     term equivalence
Ψ; Γ ⊢_i δ : Δ              local substitution
⊢_L l : Level               level well formedness
⊢_L l ≈ l' : Level          level equivalence
```

We abbreviate `Ψ; Γ ⊢_i T @ l` to `⊢_i T @ l` when `Ψ` and `Γ` are the ambient
ones, and write the ambient ones explicitly (`Ψ'; Γ' ⊢_i …`) whenever a rule
changes them. Two structural rules are always available and are never restated in
a former's section:

```
   Ψ; Γ ⊢_i t : T' @ l      Ψ; Γ ⊢_{typeof(i)} T ≈ T' @ l
  ───────────────────────────────────────────────────────  (conv)
   Ψ; Γ ⊢_i t : T @ l

   Ψ; Γ ⊢_i t : T @ l'      ⊢_L l ≈ l' : Level
  ────────────────────────────────────────────  (conv-level)
   Ψ; Γ ⊢_i t : T @ l
```

with their type-level and equivalence-level twins. Symmetry and transitivity of
both equivalences are ambient PER rules. **Layer v** admits only: the local- and
global-variable rules and their congruences, the local-substitution rules, and
the conversion rules. No rule below is available at `v`; every rule below whose
layer index is written `i` should be read as ranging over `{c, p, m}`.

### 1.4 Tarski universes: types, encodings, `El`

Types and terms are separate sorts. Types include `Ty l`, the universe at level
`l`, which itself lives at `1 + l`. Terms include *encodings* of types — the
overloaded `Nat`, `Π^{l,l'}(x:s).t`, `Ty l` at the term level — which decode into
actual types through `El^l t`:

```
   ⊢_L l : Level      Ψ; Γ ⊢_i t : Ty l @ 1 + l
  ───────────────────────────────────────────── (El-F)
   Ψ; Γ ⊢_i El^l t @ l
```

Decoding is a family of *type-equivalence* rules, e.g. ch. 04's

```
   Ψ ⊢_{typeof(i)} Γ
  ───────────────────────  (El-Nat)
   Ψ; Γ ⊢_i Nat ≈ El^0 Nat @ 0
```

Each of the six formers below therefore comes in **two** copies — a type former
and a term-level encoding — plus a decoding rule relating them. That doubling is
mechanical, but it is not optional: the code recursor's `b⃗_Typ` and `b⃗_Trm`
branch vectors are indexed by exactly these two copies, and omitting the encoding
would make the corresponding code unrepresentable.

### 1.5 The modal part and the code recursors

Layer `m` adds contextual types `□(Δ ⊢ Ty l)` (code of types) and
`□(Δ ⊢ T @ l)` (code of terms), both living at universe level **0**; the
introduction forms `box T` and `box t`; `letbox`; and the two mutually recursive
elimination principles over code,

```
Ψ; Γ ⊢_m elim^Typ (l₁,l₂) M⃗ b⃗ (l', Δ) t     : M_Typ[l'/ℓ, Δ/g, t/x_T]        @ l₁
Ψ; Γ ⊢_m elim^Trm (l₁,l₂) M⃗ b⃗ (l', Δ, T) t  : M_Trm[l'/ℓ, Δ/g, T/U_T, t/x_t]  @ l₂
```

They share two motives

```
M⃗ = (ℓ, g, x_T. M_Typ)  (ℓ, g, U_T, x_t. M_Trm)
```

well formed by the group `G_M`:

```
⊢_L l₁ : Level
⊢_L l₂ : Level
Ψ, g : Ctx;                          Γ, x_T : □(g ⊢ Ty ℓ) @ 0        ⊢_m M_Typ @ l₁   [under L, ℓ]
Ψ, g : Ctx, U_T : Typ_p(g, ℓ);       Γ, x_t : □(g ⊢ U_T^id @ ℓ) @ 0  ⊢_m M_Trm @ l₂   [under L, ℓ]
```

and a branch vector `b⃗ = b⃗_Typ b⃗_Trm` containing *one branch per code former*.
Each branch is checked against a telescope: some universe variables extending
`L`, some global variables extending `Ψ` (the sub-structures of the code being
matched), and some local variables extending `Γ` (the *recursive calls* on those
sub-structures). Ch. 04 calls those two groups `G_Typ` and `G_Trm`, and writes
`G_A := G_M G_Typ G_Trm`. **Adding a type former to DeLaM therefore means adding
branches to `G_Typ` and `G_Trm`, not merely typing and computation rules.** That
is the bulk of this document, and it is the part with no room for improvisation:
if a branch's telescope is wrong, the recursor is unsound or incomplete and
nothing else notices.

The universe level appearing in the recursive call for a sub-structure is **the
level of that sub-structure's type**, not the level of the enclosing form. Ch. 04
fixes this by the shape of the conclusion (`elim^Trm … (l', Δ, T) t` has type
`M_Trm[l'/ℓ, …]` where `l'` is `T`'s level). §16.1 records a place where the
paper and the kernel both get this wrong.

---

## 2. What we added, and why

| former | why |
|--------|-----|
| `Id`, `refl`, `J` | propositional equality. Certifying compilation needs to *state* that a source program and its lowering agree; without an identity type there is no proposition to prove. Paulin-Mohring `J` (based path induction) rather than Martin-Löf `J`, because the based form is what the elaborator generates. |
| `Σ`, `pair`, `fst`, `snd` | dependent pairs, with **projections and definitional η** rather than a `split` eliminator. Records, existentials, and every "value together with a proof about it" in the generated code are Σ. |
| `Unit`, `⟨⟩` | the terminal type, with **definitional η (proof irrelevance)** and hence *no* eliminator. It is the base case of every iterated-Σ encoding and the codomain of every trivial obligation. |
| `Empty`, `elim_Empty` | the initial type, with **definitional proof irrelevance** (§7.5). Absurdity elimination is how a lowering discharges an unreachable branch. |
| `+`, `inl`, `inr`, `case` | binary coproducts, non-dependent in the summands, with a *dependent* eliminator. Tags. |
| `W`, `sup`, `elim_W` | well-founded trees. The general branching inductive, which the tier-1 inductive lowerings compile into. |

Two design choices are worth flagging up front because they are the reason two of
the rules below are genuinely new content rather than transcription.

**Σ gets projections, not `split`.** Chapter 06's conversion is *type-directed*:
`tm_nf` dispatches on the weak-head normal form of the type. A `Σ` arm that
compares `fst a ≈ fst b` and `snd a ≈ snd b` mirrors the existing `Π` η arm
exactly, and gives definitional surjective pairing for free. A `split`
eliminator is not η-compatible and would diverge from `Π`'s treatment for no
gain. So `Σ` is a *negative* type here, like `Π`, and its η rule is a real rule
(§11.1).

**`Unit` gets η, not an eliminator.** Same reasoning taken to its limit: with
proof irrelevance at `Unit`, every term of `Unit` type is convertible to `⟨⟩` and
hence to every other, so an eliminator would be derivable and redundant. But this
means escape from the `Unit` case of the logical relation is *not derivable from
the structure of the terms* — it has to come straight from a law of the generic
equivalence (§11.2).

**`W` is positive and has no η**, which is why the finitary `Wf` former exists
later in the kernel; see §17.

---

## 3. Notation, and the contract of this document

- `↑ⁿ` is weakening by `n` local binders. `T↑` means `T` weakened past exactly the
  binders introduced between where `T` was written and where it is used; every
  occurrence below states which.
- `id_Γ` is the identity local substitution on `Γ`. `M[id_Γ, a/x]` substitutes `a`
  for the innermost binder of a `M` scoped in `(Γ, x : S @ l)` and is the
  identity on `Γ`. When two binders are discharged we write `M[id_Γ, a/y, e/p]`,
  outermost-first.
- `U^δ` / `u^δ` are global variables under a local substitution; `U^id` abbreviates
  `U^{id_Δ}` where `Δ` is the binding's own context.
- In branch telescopes, `Ψ'` lists global bindings **innermost-last**, and each
  binding's own type is scoped over the prefix of `Ψ'` before it. `Γ'` lists
  recursive-call variables in the same order.
- Congruence rules are stated compactly: for a former with premises
  `P₁ … Pₙ`, the congruence rule has premises "each `Pₖ` in equivalence form,
  plus `⊢_L lⱼ ≈ lⱼ' : Level` for every level annotation `lⱼ`, plus the original
  `Pₖ` for the left-hand side where ch. 04's `Π`/`λ` congruences ask for it", and
  concludes the equivalence of the two forms at the *left-hand* instance's type.
  Where that schema is not enough — where the rule is not a congruence — the rule
  is written in full. §11 is the list of rules that are not congruences.
- **Presupposition.** Every rule below presupposes `⊢_L Ψ` and
  `Ψ ⊢_{typeof(i)} Γ`. These are not restated as premises. Everything else is.

One warning for the Coq consumer: the rules below are stated so that a
*declarative* derivation is checkable, not so that they are syntax-directed. In
particular `refl`, `pair`, `inl`, `inr`, `sup` and the eliminators all carry full
type annotations, which makes them synthesizing in the implementation — but the
declarative rules do not depend on that, and adding an annotation-free variant
would be a conservative extension only if the annotations are recoverable, which
in the `case`/`elim_W` motive positions they are not.

---

## 4. Syntax

The grammar deltas. Additions to ch. 04 §Syntax, in its notation.

```
S, T ::=  ⋯
       |  Id^l (S; t; u)                       identity type
       |  Σ^{l,l'}(x : S). T                   dependent pair type
       |  Unit^l                               unit type
       |  Empty^l                              empty type
       |  S +^{l,l'} T                         binary sum
       |  W^{l,l'}(x : S). T                   well-founded trees

s, t ::=  ⋯
       |  Id^l (s; t; u)                       encoding of Id
       |  Σ^{l,l'}(x : s). t                   encoding of Σ
       |  Unit^l  |  Empty^l                   encodings of Unit / Empty
       |  s +^{l,l'} t                         encoding of +
       |  W^{l,l'}(x : s). t                   encoding of W
       |  refl^l (S; t)
       |  J^{l,l'} (S; a; y p. M; c; u; e)
       |  pair^{l,l'}(x : S. T; a; b)
       |  fst^{l,l'}(x : S. T; p)
       |  snd^{l,l'}(x : S. T; p)
       |  ⟨⟩^l
       |  elim_Empty^{l,l'} (x. M; t)
       |  inl^{l,l'}(A; B; a)  |  inr^{l,l'}(A; B; b)
       |  case^{l,l',l''}(A; B; z. M; x. c_l; y. c_r; t)
       |  sup^{l,l'}(x : S. T; a; f)
       |  elim_W^{l,l',l''}(x : S. T; z. M; a f ih. s; t)

b_Typ ::=  ⋯
       |  (ℓ, g, U_S, u_t, u_u, x_S, x_t, x_u. t_Id)
       |  (ℓ, ℓ', g, U_S, U_T, x_S, x_T. t_Σ)
       |  (ℓ, g. t_Unit)  |  (ℓ, g. t_Empty)
       |  (ℓ, ℓ', g, U_A, U_B, x_A, x_B. t_+)
       |  (ℓ, ℓ', g, U_S, U_T, x_S, x_T. t_W)

b_Trm ::=  ⋯
       |  (ℓ, g, u_S, u_t, u_u, x_S, x_t, x_u. t'_Id)
       |  (ℓ, g, U_S, u_t, x_S, x_t. t_refl)
       |  (ℓ, ℓ', g, U_S, u_a, U_M, u_c, u_r, u_e, x_S, x_a, x_M, x_c, x_r, x_e. t_J)
       |  (ℓ, ℓ', g, u_s, u_t, x_s, x_t. t'_Σ)
       |  (ℓ, ℓ', g, U_S, U_T, u_a, u_b, x_S, x_T, x_a, x_b. t_pair)
       |  (ℓ, ℓ', g, U_S, U_T, u_p, x_S, x_T, x_p. t_fst)
       |  (ℓ, ℓ', g, U_S, U_T, u_p, x_S, x_T, x_p. t_snd)
       |  (ℓ, g. t'_Unit)  |  (ℓ, g. t'_Empty)  |  (ℓ, g. t_triv)
       |  (ℓ, ℓ', g, U_M, u_t, x_M, x_t. t_elimE)
       |  (ℓ, ℓ', g, u_a, u_b, x_a, x_b. t'_+)
       |  (ℓ, ℓ', g, U_A, U_B, u_a, x_A, x_B, x_a. t_inl)
       |  (ℓ, ℓ', g, U_A, U_B, u_b, x_A, x_B, x_b. t_inr)
       |  (ℓ, ℓ', ℓ'', g, U_A, U_B, U_M, u_l, u_r, u_t,
              x_A, x_B, x_M, x_l, x_r, x_t. t_case)
       |  (ℓ, ℓ', g, u_s, u_t, x_s, x_t. t'_W)
       |  (ℓ, ℓ', g, U_S, U_T, u_a, u_f, x_S, x_T, x_a, x_f. t_sup)
       |  (ℓ, ℓ', ℓ'', g, U_S, U_T, U_M, u_s, u_t,
              x_S, x_T, x_M, x_s, x_t. t_elimW)
```

Note that `Unit`, `Empty` and their encodings bind a universe variable `ℓ` even
though they have no sub-structures. That is forced by level-indexing (§7.0): the
level is part of the code, so the branch must abstract it.

Note also that `+`'s branches bind two universe variables but extend no local
context — the summands are non-dependent, so both live in `g` — while `Σ`'s and
`W`'s second sub-structure lives in `(g, x : U_S^id @ ℓ)`. That difference is
what makes `t_+` *not* "`t_Σ` minus a binder" at the telescope level, even though
it looks like it.

---

## 5. `Id` — propositional equality

### 5.1 Formation

```
   ⊢_L l : Level
   Ψ; Γ ⊢_i S @ l
   Ψ; Γ ⊢_i t : S @ l
   Ψ; Γ ⊢_i u : S @ l
  ────────────────────────────────  (Id-F)
   Ψ; Γ ⊢_i Id^l (S; t; u) @ l
```

`Id` lives at the level of the type it is over. Not at `0`, and not at `1 + l`:
non-cumulativity forbids the free choice, and the code-recursor branch for `Id`
binds exactly one universe variable because there is exactly one level to name.

### 5.2 Encoding and decoding

```
   ⊢_L l : Level
   Ψ; Γ ⊢_i s : Ty l @ 1 + l
   Ψ; Γ ⊢_i t : El^l s @ l
   Ψ; Γ ⊢_i u : El^l s @ l
  ─────────────────────────────────────────  (Id-code)
   Ψ; Γ ⊢_i Id^l (s; t; u) : Ty l @ 1 + l

   ⊢_L l : Level
   Ψ; Γ ⊢_i s : Ty l @ 1 + l
   Ψ; Γ ⊢_i t : El^l s @ l
   Ψ; Γ ⊢_i u : El^l s @ l
  ──────────────────────────────────────────────────────────────  (Id-El)
   Ψ; Γ ⊢_i Id^l (El^l s; t; u) ≈ El^l (Id^l (s; t; u)) @ l
```

Only the *type* argument decodes; the two endpoints cross unchanged, since they
are already terms of `El^l s`.

### 5.3 Introduction

```
   ⊢_L l : Level      Ψ; Γ ⊢_i S @ l      Ψ; Γ ⊢_i t : S @ l
  ──────────────────────────────────────────────────────────  (refl-I)
   Ψ; Γ ⊢_i refl^l (S; t) : Id^l (S; t; t) @ l
```

`refl` synthesizes an `Id` with **syntactically identical endpoints**. Checking a
`refl` against `Id^l(S; a; b)` therefore goes through the conversion rule on the
endpoints. §12 argues why that is the load-bearing property of the whole
extension.

### 5.4 Elimination (based path induction)

```
   ⊢_L l : Level
   ⊢_L l' : Level
   Ψ; Γ ⊢_i S @ l
   Ψ; Γ ⊢_i a : S @ l
   Ψ; (Γ, y : S @ l, p : Id^l (S↑; a↑; y) @ l) ⊢_i M @ l'
   Ψ; Γ ⊢_i c : M[id_Γ, a/y, refl^l (S; a)/p] @ l'
   Ψ; Γ ⊢_i u : S @ l
   Ψ; Γ ⊢_i e : Id^l (S; a; u) @ l
  ─────────────────────────────────────────────────────────────────  (J-E)
   Ψ; Γ ⊢_i J^{l,l'} (S; a; y p. M; c; u; e) : M[id_Γ, u/y, e/p] @ l'
```

In the motive premise, `S↑` and `a↑` are weakened past the binder `y`, and the
`p` binder's own level annotation is `l` — the level of the `Id` type, which by
(Id-F) is `S`'s level.

The left endpoint `a` is *fixed*; only `u` and `e` vary. This is the
Paulin-Mohring formulation. The Martin-Löf formulation (motive over both
endpoints and the proof, case at `refl` for a variable point) is interderivable
in the presence of `Σ`, but the derivation is not definitional, so the two are
genuinely different rules and this is the one we have.

### 5.5 β

```
   ⊨ i comp
   ⊢_L l : Level
   ⊢_L l' : Level
   Ψ; Γ ⊢_i S @ l
   Ψ; Γ ⊢_i a : S @ l
   Ψ; (Γ, y : S @ l, p : Id^l (S↑; a↑; y) @ l) ⊢_i M @ l'
   Ψ; Γ ⊢_i c : M[id_Γ, a/y, refl^l (S; a)/p] @ l'
  ────────────────────────────────────────────────────────────────────────  (J-β)
   Ψ; Γ ⊢_i J^{l,l'} (S; a; y p. M; c; a; refl^l (S; a)) ≈ c
              : M[id_Γ, a/y, refl^l (S; a)/p] @ l'
```

No substitution is performed: `c` is already scoped in `Γ`.

### 5.6 η

**`Id` has no η rule.** In particular there is no rule identifying two proofs of
the same equation, and no `refl ~ ν` case relating a `refl` to a neutral. That is
deliberate: it is the absence of axiom K / UIP. (The kernel's *strict* equality
`sEq`, §17, is the deliberately proof-irrelevant sibling, and is a different
type.)

### 5.7 Congruences

Per §3's schema, for `Id-F`, `Id-code`, `refl-I` and `J-E`. Two notes. First, the
`refl` congruence compares only the points: `Ψ; Γ ⊢_i refl^l(S; t) ≈ refl^{l'}(S'; t') :
Id^l(S; t; t) @ l` from `⊢_L l ≈ l' : Level`, `⊢_i S ≈ S' @ l` and
`⊢_i t ≈ t' : S @ l`. Second, the `J` congruence must compare the motives at the
*extended* context `(Γ, y : S @ l, p : Id^l(S↑; a↑; y) @ l)` built from the
left-hand instance, and the cases at the left-hand instance's instantiated type.

### 5.8 Code-recursor branches

**`t_Id` (in `G_Typ`) — code of the type `Id^ℓ(S; t; u)`.**

```
Ψ' := Ψ, g : Ctx,
         U_S : Typ_c(g, ℓ),
         u_t : Trm_c(g ⊢ U_S^id @ ℓ),
         u_u : Trm_c(g ⊢ U_S^id @ ℓ)

Γ' := Γ, x_S : M_Typ[ℓ/ℓ, g/g, box U_S^id / x_T]                    @ l₁,
         x_t : M_Trm[ℓ/ℓ, g/g, U_S^id/U_T, box u_t^id / x_t]        @ l₂,
         x_u : M_Trm[ℓ/ℓ, g/g, U_S^id/U_T, box u_u^id / x_t]        @ l₂

Ψ'; Γ' ⊢_m t_Id : M_Typ[ℓ/ℓ, g/g, box (Id^ℓ (U_S^id; u_t^id; u_u^id)) / x_T] @ l₁
                                                                    [under L, ℓ]
```

The type argument is a `Typ_c` binding, so its recursive call `x_S` goes to the
**type** motive; the two endpoints are `Trm_c` bindings, so theirs go to the
**term** motive at type `U_S^id` and level `ℓ`. `Id` binds nothing, so all three
calls live in `g` unextended.

**`t'_Id` (in `G_Trm`) — code of the encoding.**

```
Ψ' := Ψ, g : Ctx,
         u_S : Trm_c(g ⊢ Ty ℓ @ 1 + ℓ),
         u_t : Trm_c(g ⊢ El^ℓ u_S^id @ ℓ),
         u_u : Trm_c(g ⊢ El^ℓ u_S^id @ ℓ)

Γ' := Γ, x_S : M_Trm[1 + ℓ/ℓ, g/g, Ty ℓ/U_T, box u_S^id / x_t]              @ l₂,
         x_t : M_Trm[ℓ/ℓ, g/g, (El^ℓ u_S^id)/U_T, box u_t^id / x_t]        @ l₂,
         x_u : M_Trm[ℓ/ℓ, g/g, (El^ℓ u_S^id)/U_T, box u_u^id / x_t]        @ l₂

Ψ'; Γ' ⊢_m t'_Id : M_Trm[1 + ℓ/ℓ, g/g, Ty ℓ/U_T,
                          box (Id^ℓ (u_S^id; u_t^id; u_u^id)) / x_t] @ l₂
                                                                    [under L, ℓ]
```

All three calls are at the **term** motive here, because in the encoding the type
argument is itself a code of a term (of type `Ty ℓ`). This ty/tm doubling is the
general pattern for every former: the `G_Typ` branch takes `Typ_c` globals and
recurses with `elim^Typ`; the `G_Trm` branch takes `Trm_c(… ⊢ Ty ℓ)` globals and
recurses with `elim^Trm`, with `El`-decoded binder types where there is a binder.

**`t_refl` (in `G_Trm`).**

```
Ψ' := Ψ, g : Ctx, U_S : Typ_c(g, ℓ), u_t : Trm_c(g ⊢ U_S^id @ ℓ)

Γ' := Γ, x_S : M_Typ[ℓ/ℓ, g/g, box U_S^id / x_T]              @ l₁,
         x_t : M_Trm[ℓ/ℓ, g/g, U_S^id/U_T, box u_t^id / x_t]  @ l₂

Ψ'; Γ' ⊢_m t_refl : M_Trm[ℓ/ℓ, g/g, Id^ℓ (U_S^id; u_t^id; u_t^id)/U_T,
                            box (refl^ℓ (U_S^id; u_t^id)) / x_t] @ l₂
                                                                    [under L, ℓ]
```

The `U_T` payload is the reflexive `Id` type built on the nose — there is no
global variable for it, because it is not a sub-structure of `refl`, it is
*determined* by `refl`'s two sub-structures.

**`t_J` (in `G_Trm`).** The largest branch.

```
Ψ' := Ψ, g : Ctx,
         U_S : Typ_c(g, ℓ),
         u_a : Trm_c(g ⊢ U_S^id @ ℓ),
         U_M : Typ_c((g, y : U_S^id @ ℓ, p : Id^ℓ(U_S^id↑; u_a^id↑; y) @ ℓ), ℓ'),
         u_c : Trm_c(g ⊢ U_M^{id_g, u_a^id/y, refl^ℓ(U_S^id; u_a^id)/p} @ ℓ'),
         u_r : Trm_c(g ⊢ U_S^id @ ℓ),
         u_e : Trm_c(g ⊢ Id^ℓ(U_S^id; u_a^id; u_r^id) @ ℓ)

write  g_yp := (g, y : U_S^id @ ℓ, p : Id^ℓ(U_S^id↑; u_a^id↑; y) @ ℓ)

Γ' := Γ, x_S : M_Typ[ℓ/ℓ,  g/g,     box U_S^id / x_T]                          @ l₁,
         x_a : M_Trm[ℓ/ℓ,  g/g, U_S^id/U_T, box u_a^id / x_t]                  @ l₂,
         x_M : M_Typ[ℓ'/ℓ, g_yp/g, box U_M^{id_{g_yp}} / x_T]                  @ l₁,
         x_c : M_Trm[ℓ'/ℓ, g/g, U_M^{id_g, u_a^id/y, refl^ℓ(U_S^id;u_a^id)/p}/U_T,
                                box u_c^id / x_t]                              @ l₂,
         x_r : M_Trm[ℓ/ℓ,  g/g, U_S^id/U_T, box u_r^id / x_t]                  @ l₂,
         x_e : M_Trm[ℓ/ℓ,  g/g, Id^ℓ(U_S^id; u_a^id; u_r^id)/U_T,
                                box u_e^id / x_t]                              @ l₂

Ψ'; Γ' ⊢_m t_J : M_Trm[ℓ'/ℓ, g/g, U_M^{id_g, u_r^id/y, u_e^id/p}/U_T,
                        box (J^{ℓ,ℓ'}(U_S^id; u_a^id; y p. U_M^{id_{g_yp}};
                                       u_c^id; u_r^id; u_e^id)) / x_t] @ l₂
                                                                [under L, ℓ, ℓ']
```

The motive `U_M` is a **sub-structure** (it is written in the syntax of `J`), so
it is a `Typ_c` binding with a recursive call `x_M` at the *type* motive, taken
in the extended context `g_yp`. Contrast ch. 04's `t_λ`, whose return type `U_T`
is *not* a sub-structure of `λ` and is therefore a `Typ_p` binding with no
recursive call. Whether an annotation gets a recursive call is decided by whether
the syntax carries it, not by whether it is a type.

---

## 6. `Σ` — dependent pairs

### 6.1 Formation

```
   ⊢_L l : Level      ⊢_L l' : Level
   Ψ; Γ ⊢_i S @ l
   Ψ; (Γ, x : S @ l) ⊢_i T @ l'
  ────────────────────────────────────────────  (Σ-F)
   Ψ; Γ ⊢_i Σ^{l,l'}(x : S). T @ l ⊔ l'
```

Level `l ⊔ l'`, exactly as `Π`.

### 6.2 Encoding and decoding

```
   ⊢_L l : Level      ⊢_L l' : Level
   Ψ; Γ ⊢_i s : Ty l @ 1 + l
   Ψ; (Γ, x : El^l s @ l) ⊢_i t : Ty l' @ 1 + l'
  ────────────────────────────────────────────────────────────────  (Σ-code)
   Ψ; Γ ⊢_i Σ^{l,l'}(x : s). t : Ty (l ⊔ l') @ 1 + (l ⊔ l')

   (same premises)
  ────────────────────────────────────────────────────────────────────  (Σ-El)
   Ψ; Γ ⊢_i Σ^{l,l'}(x : El^l s). El^{l'} t ≈ El^{l ⊔ l'} (Σ^{l,l'}(x : s). t)
             @ l ⊔ l'
```

Precisely ch. 04's `Π` decoding rule with `Σ` substituted for `Π`. The binder is
preserved and nothing is shifted: `El^{l'} t` is still scoped in `(Γ, x)`.

### 6.3 Introduction

```
   ⊢_L l : Level      ⊢_L l' : Level
   Ψ; Γ ⊢_i S @ l
   Ψ; (Γ, x : S @ l) ⊢_i T @ l'
   Ψ; Γ ⊢_i a : S @ l
   Ψ; Γ ⊢_i b : T[id_Γ, a/x] @ l'
  ───────────────────────────────────────────────────────────────────  (pair-I)
   Ψ; Γ ⊢_i pair^{l,l'}(x : S. T; a; b) : Σ^{l,l'}(x : S). T @ l ⊔ l'
```

### 6.4 Elimination

```
   ⊢_L l : Level      ⊢_L l' : Level
   Ψ; Γ ⊢_i S @ l
   Ψ; (Γ, x : S @ l) ⊢_i T @ l'
   Ψ; Γ ⊢_i p : Σ^{l,l'}(x : S). T @ l ⊔ l'
  ──────────────────────────────────────────────────  (fst-E)
   Ψ; Γ ⊢_i fst^{l,l'}(x : S. T; p) : S @ l

   (same premises)
  ─────────────────────────────────────────────────────────────────────  (snd-E)
   Ψ; Γ ⊢_i snd^{l,l'}(x : S. T; p) : T[id_Γ, fst^{l,l'}(x : S. T; p)/x] @ l'
```

`snd`'s result type mentions `fst` of the same pair, with the same annotations.
That self-reference is what makes projections work without a motive.

### 6.5 β

```
   ⊨ i comp
   ⊢_L l : Level      ⊢_L l' : Level
   Ψ; Γ ⊢_i S @ l
   Ψ; (Γ, x : S @ l) ⊢_i T @ l'
   Ψ; Γ ⊢_i a : S @ l
   Ψ; Γ ⊢_i b : T[id_Γ, a/x] @ l'
  ─────────────────────────────────────────────────────────────────  (fst-β)
   Ψ; Γ ⊢_i fst^{l,l'}(x : S. T; pair^{l,l'}(x : S. T; a; b)) ≈ a : S @ l

   (same premises)
  ─────────────────────────────────────────────────────────────────────  (snd-β)
   Ψ; Γ ⊢_i snd^{l,l'}(x : S. T; pair^{l,l'}(x : S. T; a; b)) ≈ b
             : T[id_Γ, a/x] @ l'
```

For `snd-β` the result type is `T[id_Γ, fst(…pair(a,b))/x]`, which is
`T[id_Γ, a/x]` by (fst-β) and the conversion rule; we state the reduced form,
which is the one the elimination rule's conclusion converts to.

### 6.6 η — **surjective pairing** (a genuinely new rule; see §11.1)

```
   ⊨ i comp
   ⊢_L l : Level      ⊢_L l' : Level
   Ψ; Γ ⊢_i S @ l
   Ψ; (Γ, x : S @ l) ⊢_i T @ l'
   Ψ; Γ ⊢_i p : Σ^{l,l'}(x : S). T @ l ⊔ l'
  ────────────────────────────────────────────────────────────────────  (Σ-η)
   Ψ; Γ ⊢_i p ≈ pair^{l,l'}(x : S. T;
                             fst^{l,l'}(x : S. T; p);
                             snd^{l,l'}(x : S. T; p))
             : Σ^{l,l'}(x : S). T @ l ⊔ l'
```

Stated in ch. 04's η direction (the expanded form on the right, as in the `Π` η
rule), and guarded by `⊨ i comp` for the same reason `Π`'s η is: at layer `c`,
code is syntax and `box p` must not be identified with `box ⟨fst p, snd p⟩`, or
the code recursor would dispatch two convertible terms to different branches.

### 6.7 Congruences

Per §3's schema for `Σ-F`, `Σ-code`, `fst-E`, `snd-E`. The `pair` congruence is
*derivable* from `Σ-η` plus the `fst`/`snd` congruences and `fst-β`/`snd-β`, and
we state it anyway for the benefit of a formalization that wants the congruence
closure to be structural:

```
   ⊢_L l₁ ≈ l₃ : Level      ⊢_L l₂ ≈ l₄ : Level
   Ψ; Γ ⊢_i S @ l₁                Ψ; Γ ⊢_i S ≈ S' @ l₁
   Ψ; (Γ, x : S @ l₁) ⊢_i T ≈ T' @ l₂
   Ψ; Γ ⊢_i a ≈ a' : S @ l₁
   Ψ; Γ ⊢_i b ≈ b' : T[id_Γ, a/x] @ l₂
  ───────────────────────────────────────────────────────────────────  (pair-cong)
   Ψ; Γ ⊢_i pair^{l₁,l₂}(x : S. T; a; b) ≈ pair^{l₃,l₄}(x : S'. T'; a'; b')
             : Σ^{l₁,l₂}(x : S). T @ l₁ ⊔ l₂
```

### 6.8 Code-recursor branches

**`t_Σ` (in `G_Typ`).** Ch. 04's `t_Π` verbatim with `Σ` for `Π`:

```
Ψ' := Ψ, g : Ctx,
         U_S : Typ_c(g, ℓ),
         U_T : Typ_c((g, x : U_S^id @ ℓ), ℓ')

write  g_x := (g, x : U_S^id @ ℓ)

Γ' := Γ, x_S : M_Typ[ℓ/ℓ,  g/g,   box U_S^id / x_T]         @ l₁,
         x_T : M_Typ[ℓ'/ℓ, g_x/g, box U_T^{id_{g_x}} / x_T] @ l₁

Ψ'; Γ' ⊢_m t_Σ : M_Typ[ℓ ⊔ ℓ'/ℓ, g/g,
                        box (Σ^{ℓ,ℓ'}(x : U_S^id). U_T^{id_{g_x}}) / x_T] @ l₁
                                                                [under L, ℓ, ℓ']
```

**`t'_Σ` (in `G_Trm`).** Ch. 04's `t'_Π` verbatim with `Σ` for `Π`:

```
Ψ' := Ψ, g : Ctx,
         u_s : Trm_c(g ⊢ Ty ℓ @ 1 + ℓ),
         u_t : Trm_c((g, x : El^ℓ u_s^id @ ℓ) ⊢ Ty ℓ' @ 1 + ℓ')

write  g_x := (g, x : El^ℓ u_s^id @ ℓ)

Γ' := Γ, x_s : M_Trm[1 + ℓ/ℓ,  g/g,   Ty ℓ/U_T,  box u_s^id / x_t]         @ l₂,
         x_t : M_Trm[1 + ℓ'/ℓ, g_x/g, Ty ℓ'/U_T, box u_t^{id_{g_x}} / x_t] @ l₂

Ψ'; Γ' ⊢_m t'_Σ : M_Trm[1 + (ℓ ⊔ ℓ')/ℓ, g/g, Ty (ℓ ⊔ ℓ')/U_T,
                         box (Σ^{ℓ,ℓ'}(x : u_s^id). u_t^{id_{g_x}}) / x_t] @ l₂
                                                                [under L, ℓ, ℓ']
```

**`t_pair` (in `G_Trm`).**

```
Ψ' := Ψ, g : Ctx,
         U_S : Typ_c(g, ℓ),
         U_T : Typ_c((g, x : U_S^id @ ℓ), ℓ'),
         u_a : Trm_c(g ⊢ U_S^id @ ℓ),
         u_b : Trm_c(g ⊢ U_T^{id_g, u_a^id/x} @ ℓ')

write  g_x := (g, x : U_S^id @ ℓ),  Σ_U := Σ^{ℓ,ℓ'}(x : U_S^id). U_T^{id_{g_x}}

Γ' := Γ, x_S : M_Typ[ℓ/ℓ,  g/g,   box U_S^id / x_T]                        @ l₁,
         x_T : M_Typ[ℓ'/ℓ, g_x/g, box U_T^{id_{g_x}} / x_T]                @ l₁,
         x_a : M_Trm[ℓ/ℓ,  g/g, U_S^id/U_T, box u_a^id / x_t]              @ l₂,
         x_b : M_Trm[ℓ'/ℓ, g/g, U_T^{id_g, u_a^id/x}/U_T, box u_b^id / x_t] @ l₂

Ψ'; Γ' ⊢_m t_pair : M_Trm[ℓ ⊔ ℓ'/ℓ, g/g, Σ_U/U_T,
                           box (pair^{ℓ,ℓ'}(x : U_S^id. U_T^{id_{g_x}};
                                            u_a^id; u_b^id)) / x_t] @ l₂
                                                                [under L, ℓ, ℓ']
```

Both type annotations are `Typ_c` sub-structures with recursive calls. That
follows ch. 04's `t_app` (which recurses on `U_S` *and* `U_T`) rather than its
`t_λ`. §16.5 flags this as a design choice rather than a forced one.

**`t_fst` and `t_snd` (in `G_Trm`).** Identical telescopes; only the branch's own
type differs.

```
Ψ' := Ψ, g : Ctx,
         U_S : Typ_c(g, ℓ),
         U_T : Typ_c((g, x : U_S^id @ ℓ), ℓ'),
         u_p : Trm_c(g ⊢ Σ^{ℓ,ℓ'}(x : U_S^id). U_T^{id_{g_x}} @ ℓ ⊔ ℓ')

Γ' := Γ, x_S : M_Typ[ℓ/ℓ,  g/g,   box U_S^id / x_T]                @ l₁,
         x_T : M_Typ[ℓ'/ℓ, g_x/g, box U_T^{id_{g_x}} / x_T]        @ l₁,
         x_p : M_Trm[ℓ ⊔ ℓ'/ℓ, g/g, Σ_U/U_T, box u_p^id / x_t]     @ l₂

Ψ'; Γ' ⊢_m t_fst : M_Trm[ℓ/ℓ, g/g, U_S^id/U_T,
                          box (fst^{ℓ,ℓ'}(x : U_S^id. U_T^{id_{g_x}}; u_p^id))
                          / x_t] @ l₂

Ψ'; Γ' ⊢_m t_snd : M_Trm[ℓ'/ℓ, g/g,
                          U_T^{id_g, fst^{ℓ,ℓ'}(x : U_S^id. U_T^{id_{g_x}}; u_p^id)/x}
                          /U_T,
                          box (snd^{ℓ,ℓ'}(x : U_S^id. U_T^{id_{g_x}}; u_p^id))
                          / x_t] @ l₂
                                                                [under L, ℓ, ℓ']
```

---

## 7. `Unit` and `Empty` — the degenerate finite types

### 7.0 Level indexing (read this before the rules)

`Unit` and `Empty` are **level-indexed, not level-polymorphic**: `Unit^l` and
`Unit^{l'}` are distinct types for `l ≉ l'`, and `⟨⟩^l` carries its level. The
alternative — a single `Unit` that checks at any level — was tried and is wrong.
Under non-cumulativity (§1.2), a type that checks at two levels is, via
`box T : □(Δ ⊢ Ty l)`, a *term* with two types, which ch. 04 §Non-cumulativity
says the code eliminator cannot survive: the branch that reconstructs the code
from its components has no level to reconstruct it at.

Concretely, this is why `t_Unit` and `t_Empty` bind a universe variable (§4)
despite having no sub-structures, and why `elim_Empty` below carries **two
independent levels**: the motive's and the scrutinee's `Empty`'s. Also note that
the issue that prompted this document states Unit η at level `0`
(`Γ ⊢ t ≈ t' : Unit @ 0`); that predates level-indexing, and the correct statement
is the one in §7.4.

### 7.1 Formation

```
   ⊢_L l : Level
  ──────────────────────  (Unit-F)
   Ψ; Γ ⊢_i Unit^l @ l

   ⊢_L l : Level
  ───────────────────────  (Empty-F)
   Ψ; Γ ⊢_i Empty^l @ l
```

Premise-free apart from the level. (Under §3's presupposition convention,
`Ψ ⊢_{typeof(i)} Γ` is ambient; a formalization that does not carry
presuppositions must add it.)

### 7.2 Encodings and decodings

```
   ⊢_L l : Level
  ─────────────────────────────────────  (Unit-code)
   Ψ; Γ ⊢_i Unit^l : Ty l @ 1 + l

   ⊢_L l : Level
  ─────────────────────────────────────  (Empty-code)
   Ψ; Γ ⊢_i Empty^l : Ty l @ 1 + l

   ⊢_L l : Level
  ────────────────────────────────────────  (Unit-El)
   Ψ; Γ ⊢_i Unit^l ≈ El^l (Unit^l) @ l

   ⊢_L l : Level
  ─────────────────────────────────────────  (Empty-El)
   Ψ; Γ ⊢_i Empty^l ≈ El^l (Empty^l) @ l
```

The encodings carry `l` for the same reason `Ty l` does at the term level: the
code is a *term*, and its type `Ty l` must be determined by it.

### 7.3 Introduction

```
   ⊢_L l : Level
  ────────────────────────────  (Unit-I)
   Ψ; Γ ⊢_i ⟨⟩^l : Unit^l @ l
```

`Empty` has no introduction rule.

### 7.4 η for `Unit` — proof irrelevance (a genuinely new rule; see §11.2)

```
   ⊨ i comp
   ⊢_L l : Level
   Ψ; Γ ⊢_i t  : Unit^l @ l
   Ψ; Γ ⊢_i t' : Unit^l @ l
  ─────────────────────────────────  (Unit-η)
   Ψ; Γ ⊢_i t ≈ t' : Unit^l @ l
```

Any two well-typed inhabitants of `Unit^l` are equivalent. Taking `t' := ⟨⟩^l`
gives the more familiar "every term is `⟨⟩`" form; the symmetric statement is
the one the logical relation needs (§11.2), so it is the one we take as
primitive. As with `Σ-η`, the `⊨ i comp` guard is essential.

Consequently **`Unit` has no eliminator**: any eliminator would be derivable, and
adding one would only give the code recursor an extra branch to dispatch on.

### 7.5 Elimination for `Empty`

```
   ⊢_L l : Level          ⊢_L l' : Level
   Ψ; (Γ, x : Empty^{l'} @ l') ⊢_i M @ l
   Ψ; Γ ⊢_i t : Empty^{l'} @ l'
  ──────────────────────────────────────────────────────────  (Empty-E)
   Ψ; Γ ⊢_i elim_Empty^{l,l'} (x. M; t) : M[id_Γ, t/x] @ l
```

The two levels are **independent**: `l` is the motive's, `l'` the scrutinee's. A
formalization must not identify them, and must not force `l' = 0`. `Empty` has no
β rule (there is no canonical form to fire on). Its η rule is proof irrelevance,
added 2026-10-07 (`docs/metatheory-ch07-extensions.md` §28), as `Unit`'s:

```
   Ψ; Γ ⊢_i t : Empty^l @ l      Ψ; Γ ⊢_i t' : Empty^l @ l
  ─────────────────────────────────────────────────────────  (Empty-η)
   Ψ; Γ ⊢_i t ≈ t' : Empty^l @ l
```

### 7.6 Congruences

Per §3's schema for all six rules above. `Unit-η` subsumes the `⟨⟩` congruence
entirely. The `elim_Empty` congruence compares both levels up to `≈`, the motives
at the extended context built from the left instance, and the scrutinees, which
`Empty-η` always equates, so an algorithm skips them.

### 7.7 Code-recursor branches

```
Ψ' := Ψ, g : Ctx
Γ' := Γ
Ψ'; Γ' ⊢_m t_Unit  : M_Typ[ℓ/ℓ, g/g, box (Unit^ℓ) / x_T]  @ l₁    [under L, ℓ]
Ψ'; Γ' ⊢_m t_Empty : M_Typ[ℓ/ℓ, g/g, box (Empty^ℓ) / x_T] @ l₁    [under L, ℓ]

Ψ'; Γ' ⊢_m t'_Unit  : M_Trm[1 + ℓ/ℓ, g/g, Ty ℓ/U_T, box (Unit^ℓ) / x_t]  @ l₂
Ψ'; Γ' ⊢_m t'_Empty : M_Trm[1 + ℓ/ℓ, g/g, Ty ℓ/U_T, box (Empty^ℓ) / x_t] @ l₂
Ψ'; Γ' ⊢_m t_triv   : M_Trm[ℓ/ℓ, g/g, Unit^ℓ/U_T, box (⟨⟩^ℓ) / x_t]      @ l₂
                                                                  [under L, ℓ]
```

Five branches, each with one universe variable, one global (`g`), and no
recursive calls. `t_Unit`/`t_Empty` mirror ch. 04's `t_Nat`; `t'_Unit`/`t'_Empty`
mirror `t'_Nat`; `t_triv` mirrors `t_ze`. The one difference from their ch. 04
models is the bound `ℓ` — `t_Nat` binds none because `Nat`'s level is fixed at
`0`.

**`t_elimE` (in `G_Trm`).** Two universe variables: `ℓ` the motive's level,
`ℓ'` the scrutinee's.

```
Ψ' := Ψ, g : Ctx,
         U_M : Typ_c((g, x : Empty^{ℓ'} @ ℓ'), ℓ),
         u_t : Trm_c(g ⊢ Empty^{ℓ'} @ ℓ')

write  g_x := (g, x : Empty^{ℓ'} @ ℓ')

Γ' := Γ, x_M : M_Typ[ℓ/ℓ,  g_x/g, box U_M^{id_{g_x}} / x_T]                @ l₁,
         x_t : M_Trm[ℓ'/ℓ, g/g, Empty^{ℓ'}/U_T, box u_t^id / x_t]          @ l₂

Ψ'; Γ' ⊢_m t_elimE : M_Trm[ℓ/ℓ, g/g, U_M^{id_g, u_t^id/x}/U_T,
                            box (elim_Empty^{ℓ,ℓ'} (x. U_M^{id_{g_x}}; u_t^id))
                            / x_t] @ l₂
                                                                [under L, ℓ, ℓ']
```

The level slot of `x_t`'s motive instantiation is `ℓ'`, the level of the
scrutinee's type `Empty^{ℓ'}` — **not** `ℓ`, the motive's. §16.1 records that the
kernel currently writes `ℓ` here, and that the same mistake is present in
ch. 04's own `t_elimN` branch.

---

## 8. `+` — binary sums

### 8.1 Formation

```
   ⊢_L l : Level      ⊢_L l' : Level
   Ψ; Γ ⊢_i A @ l
   Ψ; Γ ⊢_i B @ l'
  ────────────────────────────────────  (Sum-F)
   Ψ; Γ ⊢_i A +^{l,l'} B @ l ⊔ l'
```

Non-dependent: **both summands live in `Γ`**, neither binds. This is what makes
`+`'s recursor branches structurally unlike `Σ`'s despite the similar shape.

### 8.2 Encoding and decoding

```
   ⊢_L l : Level      ⊢_L l' : Level
   Ψ; Γ ⊢_i a : Ty l @ 1 + l
   Ψ; Γ ⊢_i b : Ty l' @ 1 + l'
  ─────────────────────────────────────────────────────  (Sum-code)
   Ψ; Γ ⊢_i a +^{l,l'} b : Ty (l ⊔ l') @ 1 + (l ⊔ l')

   (same premises)
  ─────────────────────────────────────────────────────────────────────  (Sum-El)
   Ψ; Γ ⊢_i El^l a +^{l,l'} El^{l'} b ≈ El^{l ⊔ l'} (a +^{l,l'} b) @ l ⊔ l'
```

### 8.3 Introduction

```
   ⊢_L l : Level    ⊢_L l' : Level
   Ψ; Γ ⊢_i A @ l    Ψ; Γ ⊢_i B @ l'    Ψ; Γ ⊢_i a : A @ l
  ────────────────────────────────────────────────────────────────  (inl-I)
   Ψ; Γ ⊢_i inl^{l,l'}(A; B; a) : A +^{l,l'} B @ l ⊔ l'

   ⊢_L l : Level    ⊢_L l' : Level
   Ψ; Γ ⊢_i A @ l    Ψ; Γ ⊢_i B @ l'    Ψ; Γ ⊢_i b : B @ l'
  ────────────────────────────────────────────────────────────────  (inr-I)
   Ψ; Γ ⊢_i inr^{l,l'}(A; B; b) : A +^{l,l'} B @ l ⊔ l'
```

Both injections carry **both** summands, so both synthesize.

### 8.4 Elimination

```
   ⊢_L l : Level      ⊢_L l' : Level      ⊢_L l'' : Level
   Ψ; Γ ⊢_i A @ l
   Ψ; Γ ⊢_i B @ l'
   Ψ; (Γ, z : A +^{l,l'} B @ l ⊔ l') ⊢_i M @ l''
   Ψ; (Γ, x : A @ l)  ⊢_i c_l : M[id_Γ↑, inl^{l,l'}(A↑; B↑; x)/z] @ l''
   Ψ; (Γ, y : B @ l') ⊢_i c_r : M[id_Γ↑, inr^{l,l'}(A↑; B↑; y)/z] @ l''
   Ψ; Γ ⊢_i t : A +^{l,l'} B @ l ⊔ l'
  ─────────────────────────────────────────────────────────────────────  (Sum-E)
   Ψ; Γ ⊢_i case^{l,l',l''}(A; B; z. M; x. c_l; y. c_r; t)
             : M[id_Γ, t/z] @ l''
```

In the two branch premises, `id_Γ↑` is `id_Γ` weakened past the single new binder
(`x` resp. `y`), and `A↑`/`B↑` are likewise weakened; the substituted term is the
injection of the *bound variable*.

### 8.5 β

```
   ⊨ i comp
   (all premises of Sum-E, with the scrutinee premise replaced by
    Ψ; Γ ⊢_i a : A @ l)
  ────────────────────────────────────────────────────────────────────  (case-β-l)
   Ψ; Γ ⊢_i case^{l,l',l''}(A; B; z. M; x. c_l; y. c_r; inl^{l,l'}(A; B; a))
             ≈ c_l[id_Γ, a/x]
             : M[id_Γ, inl^{l,l'}(A; B; a)/z] @ l''

   ⊨ i comp
   (all premises of Sum-E, with the scrutinee premise replaced by
    Ψ; Γ ⊢_i b : B @ l')
  ────────────────────────────────────────────────────────────────────  (case-β-r)
   Ψ; Γ ⊢_i case^{l,l',l''}(A; B; z. M; x. c_l; y. c_r; inr^{l,l'}(A; B; b))
             ≈ c_r[id_Γ, b/y]
             : M[id_Γ, inr^{l,l'}(A; B; b)/z] @ l''
```

### 8.6 η

**`+` has no η rule.** It is a positive type: its terms are generated by the two
injections, and there is no projection to expand against.

### 8.7 Congruences

Per §3's schema for all five rules. The `case` congruence compares three levels
up to `≈`, the motives in the extended context built from the left instance, and
each branch at its own instantiated type.

### 8.8 Code-recursor branches

**`t_+` (in `G_Typ`).**

```
Ψ' := Ψ, g : Ctx, U_A : Typ_c(g, ℓ), U_B : Typ_c(g, ℓ')

Γ' := Γ, x_A : M_Typ[ℓ/ℓ,  g/g, box U_A^id / x_T] @ l₁,
         x_B : M_Typ[ℓ'/ℓ, g/g, box U_B^id / x_T] @ l₁

Ψ'; Γ' ⊢_m t_+ : M_Typ[ℓ ⊔ ℓ'/ℓ, g/g, box (U_A^id +^{ℓ,ℓ'} U_B^id) / x_T] @ l₁
                                                                [under L, ℓ, ℓ']
```

Note `U_B`'s binding context is `g`, **not** `(g, x : U_A^id @ ℓ)`, and its
recursive call is likewise in `g`. That is the whole difference from `t_Σ`.

**`t'_+` (in `G_Trm`).**

```
Ψ' := Ψ, g : Ctx,
         u_a : Trm_c(g ⊢ Ty ℓ @ 1 + ℓ),
         u_b : Trm_c(g ⊢ Ty ℓ' @ 1 + ℓ')

Γ' := Γ, x_a : M_Trm[1 + ℓ/ℓ,  g/g, Ty ℓ/U_T,  box u_a^id / x_t] @ l₂,
         x_b : M_Trm[1 + ℓ'/ℓ, g/g, Ty ℓ'/U_T, box u_b^id / x_t] @ l₂

Ψ'; Γ' ⊢_m t'_+ : M_Trm[1 + (ℓ ⊔ ℓ')/ℓ, g/g, Ty (ℓ ⊔ ℓ')/U_T,
                         box (u_a^id +^{ℓ,ℓ'} u_b^id) / x_t] @ l₂
                                                                [under L, ℓ, ℓ']
```

**`t_inl` / `t_inr` (in `G_Trm`).** Both carry both summands as sub-structures,
so their premise lists differ only in where the value sits.

```
Ψ' := Ψ, g : Ctx, U_A : Typ_c(g, ℓ), U_B : Typ_c(g, ℓ'),
         u_a : Trm_c(g ⊢ U_A^id @ ℓ)            -- for t_inl
     ( or u_b : Trm_c(g ⊢ U_B^id @ ℓ')          -- for t_inr )

Γ' := Γ, x_A : M_Typ[ℓ/ℓ,  g/g, box U_A^id / x_T]                  @ l₁,
         x_B : M_Typ[ℓ'/ℓ, g/g, box U_B^id / x_T]                  @ l₁,
         x_a : M_Trm[ℓ/ℓ,  g/g, U_A^id/U_T, box u_a^id / x_t]      @ l₂
     ( or x_b : M_Trm[ℓ'/ℓ, g/g, U_B^id/U_T, box u_b^id / x_t]     @ l₂ )

Ψ'; Γ' ⊢_m t_inl : M_Trm[ℓ ⊔ ℓ'/ℓ, g/g, (U_A^id +^{ℓ,ℓ'} U_B^id)/U_T,
                          box (inl^{ℓ,ℓ'}(U_A^id; U_B^id; u_a^id)) / x_t] @ l₂

Ψ'; Γ' ⊢_m t_inr : M_Trm[ℓ ⊔ ℓ'/ℓ, g/g, (U_A^id +^{ℓ,ℓ'} U_B^id)/U_T,
                          box (inr^{ℓ,ℓ'}(U_A^id; U_B^id; u_b^id)) / x_t] @ l₂
                                                                [under L, ℓ, ℓ']
```

**`t_case` (in `G_Trm`).** Three universe variables.

```
write  Σ⁺ := U_A^id +^{ℓ,ℓ'} U_B^id
       g_z   := (g, z : Σ⁺ @ ℓ ⊔ ℓ')
       g_x   := (g, x : U_A^id @ ℓ)
       g_y   := (g, y : U_B^id @ ℓ')

Ψ' := Ψ, g : Ctx,
         U_A : Typ_c(g, ℓ),
         U_B : Typ_c(g, ℓ'),
         U_M : Typ_c(g_z, ℓ''),
         u_l : Trm_c(g_x ⊢ U_M^{id_g↑, inl^{ℓ,ℓ'}(U_A^id↑; U_B^id↑; x)/z} @ ℓ''),
         u_r : Trm_c(g_y ⊢ U_M^{id_g↑, inr^{ℓ,ℓ'}(U_A^id↑; U_B^id↑; y)/z} @ ℓ''),
         u_t : Trm_c(g ⊢ Σ⁺ @ ℓ ⊔ ℓ')

Γ' := Γ, x_A : M_Typ[ℓ/ℓ,   g/g,   box U_A^id / x_T]                       @ l₁,
         x_B : M_Typ[ℓ'/ℓ,  g/g,   box U_B^id / x_T]                       @ l₁,
         x_M : M_Typ[ℓ''/ℓ, g_z/g, box U_M^{id_{g_z}} / x_T]               @ l₁,
         x_l : M_Trm[ℓ''/ℓ, g_x/g,
                     U_M^{id_g↑, inl^{ℓ,ℓ'}(U_A^id↑; U_B^id↑; x)/z}/U_T,
                     box u_l^{id_{g_x}} / x_t]                             @ l₂,
         x_r : M_Trm[ℓ''/ℓ, g_y/g,
                     U_M^{id_g↑, inr^{ℓ,ℓ'}(U_A^id↑; U_B^id↑; y)/z}/U_T,
                     box u_r^{id_{g_y}} / x_t]                             @ l₂,
         x_t : M_Trm[ℓ ⊔ ℓ'/ℓ, g/g, Σ⁺/U_T, box u_t^id / x_t]              @ l₂

Ψ'; Γ' ⊢_m t_case : M_Trm[ℓ''/ℓ, g/g, U_M^{id_g, u_t^id/z}/U_T,
                           box (case^{ℓ,ℓ',ℓ''}(U_A^id; U_B^id;
                                  z. U_M^{id_{g_z}};
                                  x. u_l^{id_{g_x}}; y. u_r^{id_{g_y}};
                                  u_t^id)) / x_t] @ l₂
                                                          [under L, ℓ, ℓ', ℓ'']
```

---

## 9. `W` — well-founded trees

### 9.1 Formation

```
   ⊢_L l : Level      ⊢_L l' : Level
   Ψ; Γ ⊢_i S @ l
   Ψ; (Γ, x : S @ l) ⊢_i T @ l'
  ────────────────────────────────────────────  (W-F)
   Ψ; Γ ⊢_i W^{l,l'}(x : S). T @ l ⊔ l'
```

`S` are the shapes (constructor labels), `T` the branching positions at each
shape. Structurally identical to `Σ-F` and `Π-F`.

### 9.2 Encoding and decoding

```
   ⊢_L l : Level      ⊢_L l' : Level
   Ψ; Γ ⊢_i s : Ty l @ 1 + l
   Ψ; (Γ, x : El^l s @ l) ⊢_i t : Ty l' @ 1 + l'
  ──────────────────────────────────────────────────────────────  (W-code)
   Ψ; Γ ⊢_i W^{l,l'}(x : s). t : Ty (l ⊔ l') @ 1 + (l ⊔ l')

   (same premises)
  ──────────────────────────────────────────────────────────────────  (W-El)
   Ψ; Γ ⊢_i W^{l,l'}(x : El^l s). El^{l'} t ≈ El^{l ⊔ l'} (W^{l,l'}(x : s). t)
             @ l ⊔ l'
```

### 9.3 Introduction

```
   ⊢_L l : Level      ⊢_L l' : Level
   Ψ; Γ ⊢_i S @ l
   Ψ; (Γ, x : S @ l) ⊢_i T @ l'
   Ψ; Γ ⊢_i a : S @ l
   Ψ; Γ ⊢_i f : Π^{l', l ⊔ l'}(y : T[id_Γ, a/x]). (W^{l,l'}(x : S). T)↑
             @ l' ⊔ (l ⊔ l')
  ────────────────────────────────────────────────────────────────────  (sup-I)
   Ψ; Γ ⊢_i sup^{l,l'}(x : S. T; a; f) : W^{l,l'}(x : S). T @ l ⊔ l'
```

Two things a formalization must get exactly right here. First, the child function
`f`'s type is a `Π` whose **codomain level is `l ⊔ l'`** (the `W`'s own level) and
whose **domain level is `l'`** (the positions'), so by `Π`'s formation rule the
whole `Π` lives at `l' ⊔ (l ⊔ l')`. That is `≈ l ⊔ l'`, but the *syntactic* level
annotation in the kernel is the un-normalized `l' ⊔ (l ⊔ l')`, and since levels
compare by `≈` either spelling is a legal derivation; we write the un-normalized
form to match. Second, the codomain `W` is written `↑` because it sits under the
`Π`'s binder `y` and `W` is scoped in `Γ`.

### 9.4 Elimination

The step case's telescope is the most intricate object in this document, so it is
worth naming its pieces before the rule.

```
write  W    := W^{l,l'}(x : S). T
       Γ_a  := Γ, a : S @ l
       f_ty := Π^{l', l ⊔ l'}(y : T[id_Γ, a/x]). W↑     -- scoped in Γ_a
       Γ_af := Γ_a, f : f_ty @ l' ⊔ (l ⊔ l')
       ih_ty := Π^{l', l''}(y : T[id_Γ, a/x]↑).
                  M[id_Γ↑³, app(f; l', l ⊔ l'; y : T[id_Γ,a/x]↑². W↑²; y)/z]
                                                        -- scoped in Γ_af
       Γ_afi := Γ_af, ih : ih_ty @ l' ⊔ l''
```

Reading the shifts: in `Γ_a` the variable `a` sits exactly where the binder `x`
was, so `T[id_Γ, a/x]` is `T` with its binder occupied. `f_ty`'s codomain is
under `y`, hence `W↑`. `ih_ty` is written in `Γ_af`, so its domain weakens
`T[id_Γ, a/x]` past `f`; its codomain is under `y` as well, so the motive is
weakened past `a`, `f`, `y` (three binders) before `z` is substituted, and the
application's own annotations are weakened accordingly.

```
   ⊢_L l : Level      ⊢_L l' : Level      ⊢_L l'' : Level
   Ψ; Γ ⊢_i S @ l
   Ψ; (Γ, x : S @ l) ⊢_i T @ l'
   Ψ; (Γ, z : W @ l ⊔ l') ⊢_i M @ l''
   Ψ; Γ_afi ⊢_i s : M[id_Γ↑³, sup^{l,l'}(x : S↑². T↑²; a; f)↑ / z] @ l''
   Ψ; Γ ⊢_i t : W @ l ⊔ l'
  ─────────────────────────────────────────────────────────────────────  (W-E)
   Ψ; Γ ⊢_i elim_W^{l,l',l''}(x : S. T; z. M; a f ih. s; t)
             : M[id_Γ, t/z] @ l''
```

The step obligation `s` is at the motive instantiated at the *constructor form*
`sup(a, f)` — built in `Γ_af` (where `a` and `f` are the two innermost variables)
and then weakened past `ih`.

### 9.5 β — the only rule that synthesizes a λ

```
   ⊨ i comp
   ⊢_L l : Level      ⊢_L l' : Level      ⊢_L l'' : Level
   Ψ; Γ ⊢_i S @ l
   Ψ; (Γ, x : S @ l) ⊢_i T @ l'
   Ψ; (Γ, z : W @ l ⊔ l') ⊢_i M @ l''
   Ψ; Γ_afi ⊢_i s : M[id_Γ↑³, sup^{l,l'}(x : S↑². T↑²; a; f)↑ / z] @ l''
   Ψ; Γ ⊢_i a : S @ l
   Ψ; Γ ⊢_i f : Π^{l', l ⊔ l'}(y : T[id_Γ, a/x]). W↑ @ l' ⊔ (l ⊔ l')
  ─────────────────────────────────────────────────────────────────────  (W-β)
   Ψ; Γ ⊢_i elim_W^{l,l',l''}(x : S. T; z. M; a f ih. s;
                              sup^{l,l'}(x : S. T; a; f))
             ≈ s[id_Γ, a/a, f/f, IH/ih]
             : M[id_Γ, sup^{l,l'}(x : S. T; a; f)/z] @ l''
```

where the induction hypothesis is the **synthesized function**

```
IH := λ^{l', l''}(y : T[id_Γ, a/x]).
        elim_W^{l,l',l''}(x : S↑. T↑; z. M↑; a f ih. s↑;
                          app(f↑; l', l ⊔ l'; y : T[id_Γ,a/x]↑. W↑²; y))
```

Spelled out for transcription:

- `IH` is a `λ` whose **domain level is `l'`** (the positions') and whose
  **codomain level is `l''`** (the motive's) — *not* `l ⊔ l'`. Its domain type is
  `T[id_Γ, a/x]`, unshifted, since it is scoped in `Γ`.
- Inside the `λ`, all four annotations of the recursive `elim_W` (`S`, `T`, `M`,
  `s`) are weakened by exactly one binder (`y`). The three level annotations are
  *not* shifted; levels have their own variable space.
- The recursive scrutinee is the application `f y`, with `f` weakened past `y`,
  domain level `l'`, codomain level `l ⊔ l'`, domain `T[id_Γ, a/x]↑`, and
  codomain `W↑²` (once for `y`, once for the application's own `Π` binder).
- The step's three payloads are substituted **outermost-first**: `a`, then `f`,
  then `IH`.

This is the only β rule in the theory whose right-hand side contains a binder
that appears on neither side of the redex. §13 records why that matters for the
metatheory.

### 9.6 η

**`W` has no η rule.** It is positive. This is not a neutral fact: because the
children of a `sup` are stored in a `Π`, and this theory deliberately does *not*
η-expand at `Π` for code-coherence reasons at layer `c`, bridging an abstract
child function to a constructor form requires function extensionality. That cost
is exactly what motivated the kernel's later finitary `Wf` former (§17), whose
children are a `Σ`-tuple and therefore reachable by `Σ-η` and `Unit-η` alone.

### 9.7 Congruences

Per §3's schema for all five rules. The `elim_W` congruence must compare the step
terms in the full three-entry telescope `Γ_afi` built from the left instance.

### 9.8 Code-recursor branches

**`t_W` (in `G_Typ`)** and **`t'_W` (in `G_Trm`)** are `t_Σ` and `t'_Σ` with `W`
substituted for `Σ` throughout; we do not repeat them.

**`t_sup` (in `G_Trm`).**

```
write  g_x := (g, x : U_S^id @ ℓ)
       W_U := W^{ℓ,ℓ'}(x : U_S^id). U_T^{id_{g_x}}
       f_U := Π^{ℓ', ℓ ⊔ ℓ'}(y : U_T^{id_g, u_a^id/x}). W_U↑

Ψ' := Ψ, g : Ctx,
         U_S : Typ_c(g, ℓ),
         U_T : Typ_c(g_x, ℓ'),
         u_a : Trm_c(g ⊢ U_S^id @ ℓ),
         u_f : Trm_c(g ⊢ f_U @ ℓ' ⊔ (ℓ ⊔ ℓ'))

Γ' := Γ, x_S : M_Typ[ℓ/ℓ,  g/g,   box U_S^id / x_T]                     @ l₁,
         x_T : M_Typ[ℓ'/ℓ, g_x/g, box U_T^{id_{g_x}} / x_T]             @ l₁,
         x_a : M_Trm[ℓ/ℓ,  g/g, U_S^id/U_T, box u_a^id / x_t]           @ l₂,
         x_f : M_Trm[ℓ' ⊔ (ℓ ⊔ ℓ')/ℓ, g/g, f_U/U_T, box u_f^id / x_t]   @ l₂

Ψ'; Γ' ⊢_m t_sup : M_Trm[ℓ ⊔ ℓ'/ℓ, g/g, W_U/U_T,
                          box (sup^{ℓ,ℓ'}(x : U_S^id. U_T^{id_{g_x}};
                                          u_a^id; u_f^id)) / x_t] @ l₂
                                                                [under L, ℓ, ℓ']
```

Note `x_f`'s level slot: `ℓ' ⊔ (ℓ ⊔ ℓ')`, the level of `f_U`, un-normalized. It
must be the level of `x_f`'s *type*, not of the `W`.

**`t_elimW` (in `G_Trm`).** Three universe variables; the step's contextual type
carries the three-entry telescope of §9.4 verbatim.

```
write  g_x   := (g, x : U_S^id @ ℓ)
       W_U   := W^{ℓ,ℓ'}(x : U_S^id). U_T^{id_{g_x}}
       g_z   := (g, z : W_U @ ℓ ⊔ ℓ')
       g_a   := (g, a : U_S^id @ ℓ)
       f_U3  := Π^{ℓ', ℓ ⊔ ℓ'}(y : U_T^{id_{g_x}}). W_U↑²        -- in g_a
       g_af  := (g_a, f : f_U3 @ ℓ' ⊔ (ℓ ⊔ ℓ'))
       ih_U3 := Π^{ℓ', ℓ''}(y : U_T^{id_{g_x}}↑).
                  U_M^{id_g↑³, app(f; ℓ', ℓ ⊔ ℓ'; y : U_T↑². W_U↑²; y)/z}
       g_afi := (g_af, ih : ih_U3 @ ℓ' ⊔ ℓ'')

Ψ' := Ψ, g : Ctx,
         U_S : Typ_c(g, ℓ),
         U_T : Typ_c(g_x, ℓ'),
         U_M : Typ_c(g_z, ℓ''),
         u_s : Trm_c(g_afi ⊢ U_M^{id_g↑³, sup^{ℓ,ℓ'}(x : U_S↑². U_T↑²; a; f)↑/z}
                     @ ℓ''),
         u_t : Trm_c(g ⊢ W_U @ ℓ ⊔ ℓ')

Γ' := Γ, x_S : M_Typ[ℓ/ℓ,   g/g,   box U_S^id / x_T]                       @ l₁,
         x_T : M_Typ[ℓ'/ℓ,  g_x/g, box U_T^{id_{g_x}} / x_T]               @ l₁,
         x_M : M_Typ[ℓ''/ℓ, g_z/g, box U_M^{id_{g_z}} / x_T]               @ l₁,
         x_s : M_Trm[ℓ''/ℓ, g_afi/g,
                     U_M^{id_g↑³, sup^{ℓ,ℓ'}(x : U_S↑². U_T↑²; a; f)↑/z}/U_T,
                     box u_s^{id_{g_afi}} / x_t]                           @ l₂,
         x_t : M_Trm[ℓ ⊔ ℓ'/ℓ, g/g, W_U/U_T, box u_t^id / x_t]             @ l₂

Ψ'; Γ' ⊢_m t_elimW : M_Trm[ℓ''/ℓ, g/g, U_M^{id_g, u_t^id/z}/U_T,
                            box (elim_W^{ℓ,ℓ',ℓ''}(x : U_S^id. U_T^{id_{g_x}};
                                   z. U_M^{id_{g_z}};
                                   a f ih. u_s^{id_{g_afi}};
                                   u_t^id)) / x_t] @ l₂
                                                          [under L, ℓ, ℓ', ℓ'']
```

---

## 10. The code-recursor β rules

Chapter 04 gives β rules for only a selected few branches, "because there are too
many to list them all and they follow the same pattern". We state the pattern
once, precisely, and then tabulate the extension branches against it — which is
both shorter and (for a formalization) more useful than eighteen near-identical
rules.

### 10.1 The schema

Let `b_F` be the branch for a code former `F`, with telescope

```
universe variables  ℓ⃗ = ℓ₁ … ℓ_k       (innermost-last as written)
global variables    g, w₁ … w_n        (`w` ranging over `U_…` and `u_…`)
recursive calls     x₁ … x_m
```

Suppose the recursor meets a code `box (F …)` in context `Δ` — that is, the
scrutinee reduces to `box C` where `C` is an `F`-form whose sub-structures are
`c₁ … c_n` (types or terms of `Δ`) and whose level annotations are `l₁ … l_k`.
Then, with

```
φ := l₁/ℓ₁, …, l_k/ℓ_k                                (universe substitution)
σ := Δ/g, c₁/w₁, …, c_n/w_n                           (global substitution)
δ := id_Γ, r₁/x₁, …, r_m/x_m                          (local substitution)
```

where each `rⱼ` is the recursive call on the sub-structure `xⱼ` names —

```
rⱼ = elim^Typ (l₁,l₂) M⃗ b⃗ (lⱼ', Δⱼ) (box cⱼ)          if xⱼ is at the type motive
rⱼ = elim^Trm (l₁,l₂) M⃗ b⃗ (lⱼ', Δⱼ, Tⱼ) (box cⱼ)      if xⱼ is at the term motive
```

with `lⱼ'`, `Δⱼ`, `Tⱼ` read off the branch's telescope entry for `xⱼ` — the rule
is

```
   G_A       Ψ ⊢_m Γ       Ψ ⊢_p Δ       (the well-formedness premises of C in Δ)
  ────────────────────────────────────────────────────────────────────────
   Ψ; Γ ⊢_m b_F[φ][σ][δ] ≈ elim^{Typ|Trm} (l₁,l₂) M⃗ b⃗ (…, Δ [, T]) (box C)
             : M_{Typ|Trm}[…] @ l_{1|2}
```

the conclusion's type being the motive instantiated exactly as the recursor's
own typing rule (§1.5) says.

The three substitutions are applied in order `φ`, then `σ`, then `δ`, and the
recursive calls `rⱼ` are formed **before** any of them: each `rⱼ` mentions `Δⱼ`,
`Tⱼ` and `cⱼ` from the redex, not from the branch's binders.

### 10.2 The extension branches, tabulated

For each branch: the universe instantiation `φ` (written as the level list, in
the *paper's* order `ℓ, ℓ', ℓ''`), the sub-structures fed to `σ` in order, and the
recursive calls fed to `δ` in order, each written as `motive @ level, context ⊢
type`.

| branch | `φ` | sub-structures `σ` (after `Δ/g`) | recursive calls `δ` |
|---|---|---|---|
| `t_Id` | `l` | `S`, `t`, `u` | `Typ @ l, Δ`; `Trm @ l, Δ ⊢ S`; `Trm @ l, Δ ⊢ S` |
| `t'_Id` | `l` | `s`, `t`, `u` | `Trm @ 1+l, Δ ⊢ Ty l`; `Trm @ l, Δ ⊢ El^l s`; `Trm @ l, Δ ⊢ El^l s` |
| `t_refl` | `l` | `S`, `t` | `Typ @ l, Δ`; `Trm @ l, Δ ⊢ S` |
| `t_J` | `l, l'` | `S`, `a`, `M`, `c`, `u`, `e` | `Typ @ l, Δ`; `Trm @ l, Δ ⊢ S`; `Typ @ l', (Δ, y : S @ l, p : Id^l(S↑;a↑;y) @ l)`; `Trm @ l', Δ ⊢ M[id,a/y,refl^l(S;a)/p]`; `Trm @ l, Δ ⊢ S`; `Trm @ l, Δ ⊢ Id^l(S;a;u)` |
| `t_Σ` | `l, l'` | `S`, `T` | `Typ @ l, Δ`; `Typ @ l', (Δ, x : S @ l)` |
| `t'_Σ` | `l, l'` | `s`, `t` | `Trm @ 1+l, Δ ⊢ Ty l`; `Trm @ 1+l', (Δ, x : El^l s @ l) ⊢ Ty l'` |
| `t_pair` | `l, l'` | `S`, `T`, `a`, `b` | `Typ @ l, Δ`; `Typ @ l', (Δ, x : S @ l)`; `Trm @ l, Δ ⊢ S`; `Trm @ l', Δ ⊢ T[id,a/x]` |
| `t_fst`, `t_snd` | `l, l'` | `S`, `T`, `p` | `Typ @ l, Δ`; `Typ @ l', (Δ, x : S @ l)`; `Trm @ l ⊔ l', Δ ⊢ Σ^{l,l'}(x:S).T` |
| `t_Unit`, `t_Empty` | `l` | — | — |
| `t'_Unit`, `t'_Empty`, `t_triv` | `l` | — | — |
| `t_elimE` | `l, l'` | `M`, `t` | `Typ @ l, (Δ, x : Empty^{l'} @ l')`; `Trm @ l', Δ ⊢ Empty^{l'}` |
| `t_+` | `l, l'` | `A`, `B` | `Typ @ l, Δ`; `Typ @ l', Δ` |
| `t'_+` | `l, l'` | `a`, `b` | `Trm @ 1+l, Δ ⊢ Ty l`; `Trm @ 1+l', Δ ⊢ Ty l'` |
| `t_inl` | `l, l'` | `A`, `B`, `a` | `Typ @ l, Δ`; `Typ @ l', Δ`; `Trm @ l, Δ ⊢ A` |
| `t_inr` | `l, l'` | `A`, `B`, `b` | `Typ @ l, Δ`; `Typ @ l', Δ`; `Trm @ l', Δ ⊢ B` |
| `t_case` | `l, l', l''` | `A`, `B`, `M`, `c_l`, `c_r`, `t` | `Typ @ l, Δ`; `Typ @ l', Δ`; `Typ @ l'', (Δ, z : A+B @ l⊔l')`; `Trm @ l'', (Δ, x : A @ l) ⊢ M[id↑, inl x/z]`; `Trm @ l'', (Δ, y : B @ l') ⊢ M[id↑, inr y/z]`; `Trm @ l⊔l', Δ ⊢ A+B` |
| `t_W`, `t'_W` | `l, l'` | as `t_Σ`, `t'_Σ` | as `t_Σ`, `t'_Σ` |
| `t_sup` | `l, l'` | `S`, `T`, `a`, `f` | `Typ @ l, Δ`; `Typ @ l', (Δ, x : S @ l)`; `Trm @ l, Δ ⊢ S`; `Trm @ l' ⊔ (l ⊔ l'), Δ ⊢ Π^{l',l⊔l'}(y : T[id,a/x]). W↑` |
| `t_elimW` | `l, l', l''` | `S`, `T`, `M`, `s`, `t` | `Typ @ l, Δ`; `Typ @ l', (Δ, x : S @ l)`; `Typ @ l'', (Δ, z : W @ l⊔l')`; `Trm @ l'', Δ_afi ⊢ M[id↑³, sup(a,f)↑/z]`; `Trm @ l⊔l', Δ ⊢ W` |

where `Δ_afi` is §9.4's `Γ_afi` with `Δ` for `Γ`.

Two worked instances, in ch. 04's own display style, to fix the reading of the
table.

```
   G_A       Ψ ⊢_m Γ       Ψ ⊢_p Δ
   ⊢_L l : Level
   Ψ; Δ ⊢_c S @ l       Ψ; Δ ⊢_c t : S @ l       Ψ; Δ ⊢_c u : S @ l
   C   = Id^l (S; t; u)
   r_S = elim^Typ (l₁,l₂) M⃗ b⃗ (l, Δ) (box S)
   r_t = elim^Trm (l₁,l₂) M⃗ b⃗ (l, Δ, S) (box t)
   r_u = elim^Trm (l₁,l₂) M⃗ b⃗ (l, Δ, S) (box u)
  ──────────────────────────────────────────────────────────────────  (t_Id-β)
   Ψ; Γ ⊢_m t_Id[l/ℓ][Δ/g, S/U_S, t/u_t, u/u_u][id_Γ, r_S/x_S, r_t/x_t, r_u/x_u]
             ≈ elim^Typ (l₁,l₂) M⃗ b⃗ (l, Δ) (box C)
             : M_Typ[l/ℓ, Δ/g, box C / x_T] @ l₁
```

```
   G_A       Ψ ⊢_m Γ       Ψ ⊢_p Δ
   ⊢_L l : Level   ⊢_L l' : Level   ⊢_L l'' : Level
   Ψ; Δ ⊢_c S @ l
   Ψ; (Δ, x : S @ l) ⊢_c T @ l'
   Ψ; (Δ, z : W @ l ⊔ l') ⊢_c M @ l''
   Ψ; Δ_afi ⊢_c s : M[id_Δ↑³, sup^{l,l'}(x : S↑². T↑²; a; f)↑/z] @ l''
   Ψ; Δ ⊢_c t : W @ l ⊔ l'
   C   = elim_W^{l,l',l''}(x : S. T; z. M; a f ih. s; t)
   r_S = elim^Typ (l₁,l₂) M⃗ b⃗ (l, Δ) (box S)
   r_T = elim^Typ (l₁,l₂) M⃗ b⃗ (l', (Δ, x : S @ l)) (box T)
   r_M = elim^Typ (l₁,l₂) M⃗ b⃗ (l'', (Δ, z : W @ l ⊔ l')) (box M)
   r_s = elim^Trm (l₁,l₂) M⃗ b⃗ (l'', Δ_afi,
                                 M[id_Δ↑³, sup^{l,l'}(x : S↑². T↑²; a; f)↑/z])
                                (box s)
   r_t = elim^Trm (l₁,l₂) M⃗ b⃗ (l ⊔ l', Δ, W) (box t)
  ─────────────────────────────────────────────────────────────────  (t_elimW-β)
   Ψ; Γ ⊢_m t_elimW[l/ℓ, l'/ℓ', l''/ℓ'']
                    [Δ/g, S/U_S, T/U_T, M/U_M, s/u_s, t/u_t]
                    [id_Γ, r_S/x_S, r_T/x_T, r_M/x_M, r_s/x_s, r_t/x_t]
             ≈ elim^Trm (l₁,l₂) M⃗ b⃗ (l'', Δ, M[id_Δ, t/z]) (box C)
             : M_Trm[l''/ℓ, Δ/g, M[id_Δ, t/z]/U_T, box C / x_t] @ l₂
```

---

## 11. The two rules that are not congruences

Almost everything above is transcription: given ch. 04's `Π` and `Nat` rules and
the shape of a new former, the formation/introduction/elimination/β rules and all
the congruences write themselves, and the code-recursor branches follow
mechanically from which sub-structures the syntax carries. That is not a
complaint — mechanical does not mean easy, and §16 lists the places where the
mechanism was got wrong — but it does mean the *content* of this extension lives
in two rules.

### 11.1 `Σ-η` — surjective pairing

```
Ψ; Γ ⊢_i p ≈ ⟨fst p, snd p⟩ : Σ^{l,l'}(x : S). T @ l ⊔ l'
```

(§6.6 for the fully annotated form.) **Why it is not derivable, and why it must be
stated.** Chapter 07's logical relation for a negative type is
*projection-based*: the term relation at `Σ` says `w ~ w'` when
`fst w ~ fst w'` at the `S`-relation and `snd w ~ snd w'` at the instantiated
`T`-relation, for every Kripke weakening. That is the same premise shape as `Π`.
The *escape* lemma — "related terms are generically equivalent" — then has to
produce `Γ ⊢ w ≈ w'` from equivalences of the projections. With only β and the
`fst`/`snd` congruences available, escape is stuck exactly when one side is a
literal pair and the other is neutral: the projections agree, but nothing
identifies the two terms themselves.

Surjective pairing is what closes that gap, and it closes it on **both**
instantiations of the generic equivalence. On the algorithmic side, `conv.rs`
supplies it as a type-directed η arm that fires on literal pairs, neutrals, and
mixtures alike. On the declarative side there was, until this document, nothing.
Ch. 08's soundness argument for the checker therefore had nothing to land on: we
were asserting completeness of the algorithm against a specification whose
`Σ` case could not be escaped.

Note that under the negative reading `Σ-η` is *not* a separate semantic
obligation in the logical relation — both sides of the equation have the same
projections up to β, which is the whole point of choosing projections over
`split`. It is an obligation on the *syntactic* equivalence only. That asymmetry
is why it is easy to forget.

### 11.2 `Unit-η` — proof irrelevance

```
Ψ; Γ ⊢_i t ≈ t' : Unit^l @ l          for any well-typed t, t'
```

(§7.4.) **Why it is not derivable.** The logical relation at `Unit` is the
standard irrelevant one: `t ~ t'` iff both are well typed at `Unit`, with no
weak-head condition and no case analysis. That is what makes every property
lemma at `Unit` (weakening, symmetry, transitivity, irrelevance, reflexivity of
neutrals, weak-head expansion, layering restriction) hold vacuously. The price is
that escape at `Unit` is not readable off the structure of the terms *at all* —
there is no structure. It must come straight from a law of the generic
equivalence, and that law is this rule.

Two consequences are worth recording because they are unusual and a
formalization will hit both.

*Presupposition is not recoverable from the rule.* The rule relates any two terms
that are well typed at `Unit^l`, and the algorithm implements it by returning
success without inspecting either side, so it also relates ill-typed junk. Ch. 08
states its laws for well-typed inputs and the kernel only invokes conversion on
well-typed input, so the law survives — but it survives *by assumption on the
caller*, not by the structure of the rule. A formalization that wants
presupposition as a theorem must carry the well-typedness premises explicitly, as
§7.4 does.

*Order matters algorithmically, not declaratively.* For completeness, the η arm
must be tried before any structural fallback (otherwise `⟨⟩` versus a neutral
fails). That is a fact about the algorithm; the declarative rule has no order.
§16.10.

### 11.3 Why both are guarded by `⊨ i comp`

Both rules sit in the computation-rule group, alongside `Π`'s β and η. That is
not a stylistic choice. At layer `c`, code is syntax: `box t` and `box t'` are
convertible only when `t` and `t'` are syntactically equal, and the code recursor
dispatches on exactly that syntax. If `Unit-η` fired at `c` then `box ⟨⟩^l` and
`box ν` would be convertible while `elim^Trm` still sent them to `t_triv` and to
the variable branch respectively — the recursor would observe a distinction that
conversion had erased, and coherence would fail. The same argument applies to
`Σ-η`, and it is *the same argument* that forces δ to be indexed by the layer
(§14.2). Layering is what buys these η rules without giving up intensional
analysis.

---

## 12. The `refl`-endpoints-by-conversion invariant

This is not a rule; it is a property of the rules above, and it is the reason
adding a propositional equality to a theory with intensional code analysis is
consistent at all. It deserves to be stated wherever the rules are.

Consider `Id^0(□(Δ ⊢ T @ l); box t; box t')` — propositional equality between two
pieces of *code*. When is it inhabited?

1. `refl^l(S; a)` **synthesizes** `Id^l(S; a; a)` (§5.3), with syntactically
   identical endpoints. So checking a `refl` against `Id^0(□(…); box t; box t')`
   goes through the **conversion rule** on the endpoints: it succeeds iff
   `Ψ; Γ ⊢_p box t ≈ box t' : □(Δ ⊢ T @ l) @ 0`.
2. Conversion at a contextual type is **syntactic identity** (modulo level
   equivalence): ch. 04 gives no rule identifying two boxes of distinct code, and
   ch. 06 compares boxed payloads structurally. This matches the logical
   relation's `j = m` case, in which `box t` is related only to itself.
3. Therefore `Id^0(□(Δ ⊢ T @ l); box t; box t')` is inhabited by `refl`
   **iff `t` and `t'` are syntactically equal code** — which is exactly the
   equality the code recursors dispatch on.

So propositional equality at `□` is precisely as fine as the recursor's
observation: no coarser, no finer. There is no rule in the other direction —
`J` eliminates an `Id` into a motive, it never produces a definitional
equivalence, and there is no unboxing congruence — so the two cannot drift apart
from that side either.

**The invariant this rests on, stated once:** *endpoint checking goes through
conversion, and conversion at `□` is syntactic identity modulo level
equivalence.* Relax **either** half — a "conversion up to β for code"
convenience, or an `Id` rule that bypasses endpoint conversion (a definitional or
irrelevant identity type would be one) — and the observation and the equality
part company, at which point the consistency argument above has to be redone from
scratch. Treat both halves as invariants of the design, not as implementation
details. (The kernel's `sEq` shares the property, for the same two reasons, so a
change here moves both observers at once.)

---

## 13. `W`'s infinitary Kripke term relation

A note for anyone extending the ch. 07 metatheory rather than the ch. 04 rules,
recorded here because it is the one place where an extension changes the *shape*
of the semantics rather than adding a case.

The type relation at `W` mirrors `Σ`'s and `Π`'s: both sides reduce to `W`-forms,
the whnfs are generically equivalent, `E :: ∀ψ. S₁ ~ S₂ @ l`, and
`F :: ∀ψ, ∀ s ~ s' @ E(ψ). T₁[s/x] ~ T₂[s'/x] @ l'`. The *term* relation is where
it changes. `NfEqW` says:

- `sup(a, f) ~ sup(a', f')` when `a ~ a' @ E(id)` **and** for every Kripke
  weakening `ψ` and every `b ~ b' @ F(ψ, …)`, the subtrees `f b` and `f' b'` are
  related by `NfEqW` again;
- `ν ~ ν'` for generically equivalent neutrals.

`NfEqW` is therefore an **infinitary, Kripke-quantified inductive definition**:
the recursive occurrence sits under `∀ψ. ∀ b ~ b'. …`. It is strictly positive,
so it is a legitimate inductive definition, but it is a new shape in this
development. `NfEqNat` recurses finitarily; `Π`'s quantification lives in the
*type* relation, which is defined by recursion on levels rather than by
induction. `W` is the first place the two are combined.

The Kripke quantifier is not decoration. In the fundamental theorem's `elim_W`
arm one must supply the semantic step premise with three related arguments, and
the third is the λ that `W-β` (§9.5) synthesizes. Showing
`λy. elim_W(…; f y) ~ λy. elim_W(…; f' y)` unfolds through the `Π` term relation
to: for every `ψ` and every `b ~ b'`, the two applications are related. Those
applications weak-head-reduce to `elim_W(…; f b)` and `elim_W(…; f' b')`, and
*those* are related by the inner induction hypothesis of `NfEqW` — which is
exactly the `∀ψ`-quantified subtree premise the `sup` case carries. **A
non-Kripke formulation would not survive the application under a weakening.**

Both `Π`'s and `Σ`'s premises are contravariant (they quantify over related
arguments), and so is `W`'s `F`; the layering-restriction lemma for all three
therefore needs the iff-strengthened induction hypothesis, not the one-directional
one.

---

## 14. Definitions: bodied global bindings and δ

A seventh extension, different in kind: not a type former but a *binding* form.
Recorded here because it is ch. 04-shaped and belongs in the same ledger. (These
rules were first written down in `docs/metatheory-ch07-extensions.md` Part IV,
which said they belonged in this document once it existed; this is that
document.)

### 14.1 The binding form and its typing

Ch. 04's global bindings are declarations only. We add a body to the third:

```
B ::= g : Ctx | U : Typ_i(Δ, l) | u : Trm_i(Δ ⊢ T @ l) | u : Trm_i(Δ ⊢ T @ l) := t
```

with the well-formedness rule extending `⊢_L Ψ`:

```
   ⊢_L Ψ          ⊢_L l : Level          Ψ ⊢_p Δ          Ψ; Δ ⊢_p T @ l
   Ψ; Δ ⊢_i t : T @ l          i = c
  ─────────────────────────────────────────────────────────────────────  (wf-def)
   ⊢_L Ψ, u : Trm_i(Δ ⊢ T @ l) := t
```

Three deliberate constraints:

1. **`i = c`.** Layer `v` admits only variables, so a definition there would be a
   renaming with extra steps; and the binding invariant already forbids `p` and
   `m`.
2. **The body is checked at the binding's own layer `i`**, not at `p`. This is
   what makes δ *layer-preserving*: unfolding `u` at any `j ≥ i` produces a term
   already legal at `j`. Checking at `p` instead would let `box (u^δ)` be code
   whose unfolding is not code, and preservation at `p` would fail.
3. **The body is scoped in `Δ` over `Ψ`'s prefix**, exactly like `T` — so an
   occurrence at `Ψ, Ψ'` unfolds to `t⇑^{|Ψ'|+1}[δ]`.

The *use* rules are unchanged: `Ψ; Γ ⊢_j u^δ : T[δ] @ l` for `i ≤ j` is ch. 04
verbatim. A definition is a declaration that additionally knows its body, which
is why this is one binding form and not two.

### 14.2 δ, and why it is indexed by the layer

```
   u : Trm_c(Δ ⊢ T @ l) := t  ∈ Ψ          ⊨ j comp
  ─────────────────────────────────────────────────  (δ)
   Ψ; Γ ⊢_j u^δ ⇝ t[δ] : T[δ] @ l
```

and correspondingly `u^δ` is **not** neutral at a computing layer when `u` is
defined, while it stays neutral at `c`.

The layer index is forced, not chosen — by the same argument as §11.3. Ch. 06
blocks both code-recursion principles on global variables and compares
`box (U^δ)` / `box (u^δ)` syntactically. If δ fired at `c`, then
`box (u^δ) ≈ box t` while `elim^Trm` still dispatched them to different branches:
the recursor would observe a distinction conversion had erased. So at `p`/`m`,
`u` denotes its body (running is prog's business); at `c`, `u` denotes itself
(code is syntax).

Two invariants:

- **Type-level bindings stay opaque at every layer.** `U : Typ_i(Δ, l)` gains no
  body, so a type reaches δ only through `El ν`.
- **δ never enters a `box`.** Reduction does not descend into `box`, and boxed
  code compares by syntactic equality, so the layer-`c` guarantee is structural
  rather than a check that could be forgotten.

### 14.3 Conversion order

Algorithmically, weak-head reduction runs first *without* δ; if both sides then
sit at the same defined head, their spines are compared first, and only a failure
unfolds. **Declaratively this is not a rule at all** — δ is a reduction and the
spine comparison is the ordinary neutral congruence — so ch. 08's
soundness/completeness story is unaffected in shape. The heuristic changes which
derivation the algorithm finds, not which pairs are related. It is listed in §16
as a divergence candidate for exactly that reason: the specification must not
fix it.

---

## 15. Summary of what each former owes

| former | β | η | new rule (not a congruence) | code branches added |
|---|---|---|---|---|
| `Id` | `J`-on-`refl` | — | — | `t_Id`, `t'_Id`, `t_refl`, `t_J` |
| `Σ` | `fst`/`snd`-on-`pair` | **surjective pairing** | §11.1 | `t_Σ`, `t'_Σ`, `t_pair`, `t_fst`, `t_snd` |
| `Unit` | — | **proof irrelevance** | §11.2 | `t_Unit`, `t'_Unit`, `t_triv` |
| `Empty` | — | — | — | `t_Empty`, `t'_Empty`, `t_elimE` |
| `+` | `case`-on-`inl`/`inr` | — | — | `t_+`, `t'_+`, `t_inl`, `t_inr`, `t_case` |
| `W` | `elim_W`-on-`sup` (synthesizes a λ) | — | — | `t_W`, `t'_W`, `t_sup`, `t_elimW` |

Twenty-two new code-recursor branches, six new type formers, six new encodings,
six new decoding rules, and two new rules of the equivalence.

---

## 16. Remarks: where the specification and the algorithm could — or do — differ

The point of writing a declarative specification down next to an existing
implementation is to find the seams. These are the ones we found. Items 16.1 and
16.2 are candidates for genuine defects; the rest are places where the
implementation makes a choice a specification should deliberately *not* fix.

### 16.1 A genuine mismatch: the scrutinee's recursive-call level in the eliminator branches

This is the one item here that looks like a bug rather than a divergence, and it
is inherited from ch. 04.

The recursor's conclusion (§1.5) pins the convention: `elim^Trm … (l, Δ, T) t`
has type `M_Trm[l/ℓ, Δ/g, T/U_T, t/x_t]` where **`l` is the level of `T`**. So a
recursive call on a sub-structure of type `X @ l_X` must instantiate the term
motive's `ℓ` at `l_X`.

In `t_elimE` (§7.7), the scrutinee `u_t` has type `Empty^{ℓ'} @ ℓ'`, so `x_t`'s
declared type must be `M_Trm[ℓ'/ℓ, …]`. The kernel declares it at `M_Trm[ℓ/ℓ, …]`
— the *motive's* level — while the β rule supplies a recursive call
`elim^Trm(scrut_level, Δ, Empty^{scrut_level}, scrut)` whose type is
`M_Trm[scrut_level/ℓ, …]`. The two disagree in the `ℓ` slot whenever `M_Trm`
actually mentions `ℓ` and the two levels are not equivalent.
(`crates/kernel/src/rec.rs`, the `tm_elim_empty` spec, `x_t`'s
`inst_tm_motive(…, lvar(1), …, Empty{lvar(0)}, …)`; against
`crates/kernel/src/reduce.rs`'s `ElimEmpty` arm,
`rec.elim_tm(scrut_level, …)`.)

The same pattern is present in the kernel's `t_elimN` branch — `x_t` at
`M_Trm[ℓ/ℓ, …, Nat/U_T, …]` where `Nat` lives at `0`, against a β rule that
supplies the call at level `0` — and *there* the kernel is faithfully
transcribing ch. 04, which writes `M_Trm[ℓ/ℓ, g/g, Nat/U_T, box u_t^id/x_t]` in
the `t_elimN` telescope. Compare the paper's own `t_ze` and `t_succ` branches,
which correctly write `0/ℓ` for a `Nat`-typed sub-structure, and its `t_El`
branch, which correctly writes `1 + ℓ/ℓ` for a `Ty ℓ`-typed one. So `ℓ/ℓ` in
`t_elimN` reads as a typo in ch. 04 that the kernel inherited and then repeated
when `Empty` was level-indexed.

**The correct rule is the one in §7.7** (`ℓ'`, the scrutinee's level). This
document states the rule; per the terms of this round, no code was changed. The
kernel is not observably broken today only because the motives that reach these
branches do not depend on `ℓ` in a way that distinguishes the two levels; that is
luck, not design. It is worth an issue.

**Resolved (2026-08-06, `recursor-elim-call-level-mismatch`).** The kernel now
follows §7.7 at all three affected branches — `t_elimN` (`0/ℓ`, `Nat`'s level),
`t_elimE` and `t_elim_sE` (`ℓ'/ℓ`). One further fact the fix turned up, worth
recording because it explains the latency more sharply than "no motive
distinguishes the levels" does: under the identity motives the *old* entry was
not merely mis-levelled but **ill-formed** — `M_Trm[ℓ/ℓ, Empty^{ℓ'}/U_T, …]`
unfolds to `□(g ⊢ Empty^{ℓ'} @ ℓ)`, and `Empty^{ℓ'}` does not live at `ℓ`. A
branch could therefore never *use* the entry, which is why nothing ever
complained. With an `ℓ`-dependent but `U_T`-independent motive (e.g.
`M_Trm := □(g ⊢ Ty ℓ)`) the old entry is well-formed and the mismatch is a
genuine subject-reduction failure, so the defect was real, not merely untidy.

### 16.2 β rules do not check the constructor's own annotations

Every β rule in the kernel fires on the *head shape* of the eliminand and ignores
that eliminand's annotations: `J` fires on any `refl` whatever its level, type,
or point; `fst`/`snd` fire on any `pair` whatever its four annotations;
`case` fires on any `inl`/`inr`; `elim_W` fires on any `sup`. The reduct is built
entirely from the *eliminator's* annotations.

This is correct — reduction in ch. 06 is untyped, so it *cannot* check them, and
on well-typed input the annotations agree by inversion — but it means the
declarative β rules above (which state the redex with matching annotations on
both forms) and the algorithm are not in literal correspondence. The gap is
closed by the preservation lemma, not by the rules. A formalization has a choice:
state β with matching annotations, as §§5.5/6.5/8.5/9.5 do and prove the
algorithm sound via inversion; or state β with independent annotations plus
equivalence premises. We chose the former because it matches ch. 04's own `Π`-β,
and flag it because the choice is invisible in the rules.

### 16.3 `El` decoding discards the `El`'s own level

The decoding rules (§5.2, §6.2, §7.2, §8.2, §9.2) state the `El`'s level as
determined by the encoding's. The implementation's type reduction takes the head
of the `El`'s argument and rebuilds the reduct from *that* term's level fields,
discarding the `El` node's own `level` entirely — so operationally it implements
`El^{anything} (Σ^{l,l'} s t) ⇝ Σ^{l,l'}(El^l s, El^{l'} t)`. Level agreement is
maintained by typing and preservation, not by the reduction. Again: correct,
untyped, and not literally the declarative rule.

### 16.4 `Unit`'s conversion arm relates ill-typed terms

Discussed in §11.2. The algorithm's `Unit` arm returns success without inspecting
either side, which is a strictly larger relation than `Unit-η` as stated (which
carries two well-typedness premises). Soundness of the algorithm against the spec
therefore holds only for well-typed inputs — which is the standing assumption of
ch. 08 and the kernel's calling convention, but it is an assumption, and a
formalization must carry it rather than derive it.

### 16.5 Whether an annotation is a code-recursor sub-structure is a design choice

Ch. 04 makes a point of demonstrating both options: `t_app` recurses on the
domain *and* codomain annotations of an application (both are `Typ_c` bindings
with recursive calls), while `t_λ` treats a `λ`'s codomain as an *external* index
— a `Typ_p` binding with **no** recursive call — because a `λ` does not carry it
in its syntax. The paper explicitly notes the alternative
(`λ^{l,l'}(x:S). (t : T)`) and says it chose to show both.

Our extensions all follow `t_app`: `t_pair`, `t_fst`, `t_snd`, `t_inl`, `t_inr`,
`t_sup` all recurse on both type annotations, because our introduction forms all
carry them (which is also what makes them synthesize). One visible consequence is
that `t_fst`/`t_snd` (eliminators) and `t_inl`/`t_inr` (introductions) end up
with premise lists of the same shape. This is a legitimate design choice, not a
forced one, and a re-formalization could reasonably make the opposite one for the
introduction forms. The specification should not present it as forced. It is
forced only for `case` and `elim_W`, whose motives *must* be sub-structures
because they cannot be recovered from anything else.

### 16.6 Un-normalized level annotations

`sup`'s child-function type lives at `l' ⊔ (l ⊔ l')`, and `elim_W`'s `f` and `ih`
context entries similarly. Because levels compare by `≈`, the collapsed `l ⊔ l'`
and `l' ⊔ l''` are equally valid annotations, and the kernel and its own doc
comments differ on which they write. The specification above writes the
un-normalized form, to match the implementation; a formalization is free to
normalize, and must not treat either spelling as canonical.

### 16.7 `elim_Empty`'s two levels

The two levels on `elim_Empty` are independent, and `Empty^{l'}` is genuinely
level-indexed rather than fixed at `0`. A specification written before
level-indexing would naturally fold them into one (or force `l' = 0`) and would
then be *stricter* than the implementation, rejecting programs the kernel accepts.
The reason for level-indexing is §7.0, and it is a consequence of
non-cumulativity, not a convenience.

### 16.8 Stuck-but-not-neutral configurations

The implementation's neutrality predicates deliberately do not classify
configurations like `fst (λx. t)`, `case(…; sup(…))`, `elim_W(…; pair …)`,
`J(…; ⟨⟩)`. These are irreducible and non-neutral: they are outside the
well-typed fragment. A declarative specification says nothing about them and
should not; a formalization that defines a *total* normal-form predicate will
find them and must classify them as ill-typed rather than adding rules.

### 16.9 Reduction order and congruence positions

The implementation's step relation is a *function*: at each node exactly one
subterm is chosen for congruence (the eliminand), and motives, branches, and all
type annotations are never reduced. The declarative equivalence is a congruence
in *every* position. This is a weak-head-strategy choice with no semantic
content, and the specification must not fix it. (One place where the choice does
leak into the implementation's *grammar* is `elim^Trm`'s type annotation, which
reduction fixes as reducing before the scrutinee, forcing the neutral predicate
to require the annotation be in whnf. Ch. 04's grammar leaves it unconstrained.)

### 16.10 η ordering, and δ ordering

Both `Σ-η` and `Unit-η` must be tried before any structural fallback for the
algorithm to be complete; δ-lazy conversion (§14.3) compares spines before
unfolding. Neither is a rule. Both change which derivation the algorithm finds,
not which pairs are related, and a specification that fixed either would be
over-specified.

### 16.11 Stale documentation in the kernel (not rule defects)

Noticed while transcribing, recorded so it is not lost: several `Branches` doc
comments in `crates/kernel/src/term.rs` describe `t_Unit`/`t_Empty`/`t_triv` and
`t_elimE` telescopes with one fewer universe binder than the code actually binds
(the level-indexing round added them); `typing.rs`'s module docs say the recursor
checks "45 branches" where the current count is 52; and the `sEq`/`sEmpty`
comments still say those formers are "gated out of layer c until the rec.rs
round", a gate that no longer exists anywhere in the crate. All three are comment
drift, not rule or code defects, and none affects anything in this document
beyond making the telescopes harder to read off.

**Resolved (2026-08-06, `kernel-doc-comments-stale`).** All three corrected in
the same round: the `Unit`/`Empty`/`⟨⟩`/`t_elimE` telescopes in `term.rs` and
`rec.rs` now carry their level binders, the branch count reads 52, and the
layer-c gate wording is gone from `term.rs` (`SEq`, `SEmpty`, `SRefl`,
`Transp`, `ElimSEmpty`, `Vec`).

---

## 17. Deliberately not covered

The kernel has five more formers, all added after the six above and all with
their own design documents. They are out of scope here, and listing them is part
of the specification:

- **`sEq` / `srefl` / `transp`** — strict, definitionally proof-irrelevant
  equality. `sEq`'s formation rule is `Id`'s verbatim; its *term* relation is
  `Unit`'s (any two proofs are equal), which is where all the content is. Its
  conversion additionally has a *strip* rule keyed on the endpoints rather than
  the proof. See `docs/sprop-design.md` and
  `docs/metatheory-ch07-extensions.md` Part III.
- **`sEmpty` / `elim_sEmpty`** — the strictly irrelevant empty type; `Empty`'s
  rules with an irrelevance arm.
- **`Vec` / `Fin`** — the `Σ`-tuple and canonical finite-index families. Neither
  is a new logical-relation case: both are *reducing* type formers
  (`Vec^l(T; 0) ⇝ Unit^l`, `Fin(S k) ⇝ Unit + Fin(k)`), so the η they appear to
  have is inherited through the reduction from `Σ` and `Unit`. This is the first
  place §11's two rules pay for something beyond themselves.
- **`Wf` / `sup_f` / `elim_Wf`** — the finitary branching fixed point, whose
  children are a `Vec` rather than a `Π`. It exists precisely because `W` has no
  η (§9.6): bridging an abstract child function to a constructor form at `W`
  needs funext, while the same bridge at `Wf` descends through `Σ`-η and bottoms
  out in `Unit`'s proof irrelevance — a conversion. See
  `docs/branching-inductives-choice.md` and `docs/wf-former-design.md`.

Writing these six down properly is what makes the seventh cheap; that was the
motivation for this document, and the four above are the evidence that it works.

Also out of scope, as noted in §0: the ch. 06 side (weak-head-normal and neutral
grammars, algorithmic convertibility) for the new formers, and the ch. 07 logical
relation itself beyond the summaries in §11 and §13.

---

## Sources

- `docs/delam/04_dependent_layered_modal_type_theory.tex` — the system being
  extended; notation, rule style, and the `G_A` telescope this document mirrors.
  Also `docs/delam/README.md` for the errata found while implementing.
- `docs/metatheory-ch07-extensions.md` — the ch. 07 pen-and-paper pass. §7 is the
  section that identified §11's two rules as owed; §§3–6 are the logical-relation
  cases summarized in §11 and §13; Part IV §§23–25 are §14 of this document.
- `crates/kernel/DESIGN.md` — the kernel's own record of the design choices in §2
  and the invariant in §12.
- `crates/kernel/src/typing.rs`, `reduce.rs`, `rec.rs`, `term.rs`, `conv.rs` —
  the implementation these rules were transcribed from, and against which §16's
  divergences were found.
- `docs/unit-empty-level-indexing.md` — why §7.0.
