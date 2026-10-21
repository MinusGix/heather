# The `IWf` former: finitary inductive families without a stored equation

Status: **rule set (§1–§6) reviewed and frozen, 2026-10-13**; `DVec` and
`dnth` in the kernel (§13 step 2, 2026-10-17), `IWf`/`sup_i`/`elim_IWf`
in the kernel (§13 step 3, 2026-10-20); the codes (step 4) not yet. §7–§13 stay open where §12 says so: they are the generator's, not the
kernel's. The review's edits are §1's layer paragraph, §1.1's and §10's
neutral-length caveat, and §3's note on the ih's type. It is
[[indexed-families]]'s route 4, promoted, and extended with an output-index
function. Tracking issue: `issues/iwf-former.md`. Written before the code,
per repo discipline, as the specification an implementation would be
checked against. The evidence so far is a Coq probe, listed in §11. It
checks the derived `dnth`, β on open data, three of the lowerings and
index inversion. The Coq formalization has since checked §1–§6 (heather-coq
`M17_DESIGN.md`), and the kernel follows its de Bruijn transcriptions.

The design principle, stated once: **an index constraint belongs in the
type of a constructor, not in its data.** Route 2b stores the equation
`μ s = m` in every value and needs strict irrelevance to make the stored
proof invisible, plus a computing `transp` to use it. Both have turned
out to cost more than the round priced:

- `transp` into relevant motives, together with `sEq`'s irrelevance and
  β at `srefl`, proves UIP for `Id`. The proof takes four lines, and
  `sEq`'s irrelevance plus propositional β suffice. It is GCST's
  "without K" point, checked in Coq
  ([[sprop-strip-normalization-open]]).
- The strip is Werner's rule. Whether it preserves normalization in a
  predicative theory is Abel–Coquand's open question (3) (same issue).

A former whose constructor *is* at its result index stores nothing. There
is then nothing to make irrelevant and nothing to transport.

---

## 1. New formers

Two. `DVec` is `Vec` with a per-position element type; `IWf` is `Wf` with
an index.

**Layers: as `Wf`'s.** `DVec`, `IWf`, `sup_i` and `elim_IWf` are gated out
of layer c until the rec.rs round (§13 step 4) gives them their code-recursor
branches, as `Wf`'s formers were (`wf-former-design.md` §8 step 5), and are
code after it. The Coq formalization types them at its layers D and M and
reaches C through codes and static code. For `Wf` that meant porting `nth`'s
typing to C by hand, since `nth` types only through `Fin`'s and `Vec`'s
computation rules (its M15b, `nth_wf_g`); `dnth` needs the same port.

### 1.1 `DVec`: dependent fixed-length tuples

```
Γ ⊢ k : Nat        Γ, i : Fin k ⊢ F : Type @ l
-----------------------------------------------
Γ ⊢ DVec^l(k; i. F) : Type @ l

DVec^l(0;   i. F)  ⇝  Unit^l
DVec^l(S k; i. F)  ⇝  Σ^{l,l}(_ : F[inl ⟨⟩/i]). DVec^l(k; j. F[inr j/i])
```

It takes a binder, not a family argument, because Heather has no
type-valued functions. As with `Vec`, it reduces on a canonical length
and is neutral at a neutral one, with no η of its own. η arrives through
the reducts. `Vec^l(T; k)` and `DVec^l(k; _. T)` agree reduct for
reduct at a canonical length. At a neutral length they are two distinct
neutral types and do not convert, so the two must not both be spellings of
one type: either `Vec` is the only spelling of a constant-family tuple, or
it is gone (§10). So `Vec` could become derived, or stay a former for its
`Conv::vec_ty` fast path (`wf-former-design.md` §5). That is an
implementation choice, recorded in §10.

### 1.2 `IWf`: the finitary indexed fixed point

```
Γ ⊢ I : Type @ li
Γ ⊢ S : Type @ l
Γ, x : S ⊢ n : Nat                       (arity)
Γ, x : S ⊢ o : I                         (output index)
Γ, x : S, i : Fin n ⊢ c : I              (child index at position i)
Γ ⊢ m : I
--------------------------------------------------------------
Γ ⊢ IWf^{l,li}(I; x:S. n; x. o; x i. c)(m) : Type @ l ⊔ li
```

These are Dybjer's finitary inductive families in `Wf`'s shape. The
constructor's result index is a function of its shape (`o`), and each
child's index is a function of the shape and the position (`c`). `Wf` is
the instance `I := Unit` with trivial `o` and `c`.

**The level is `l ⊔ li`** (decided 2026-09-30). The codes force it:
`TmIWf` carries the index type's code, at `li`, and a code at `Ty l` cannot
contain one from a higher level. The same reason puts `Σ^{l,li}` at
`l ⊔ li` and `Id` at its carrier's level. In practice it is `l`: index
types are `Nat` or declared data at level 0, and today's forded families
(`Σ^{l,li}(s). sEq^{li}(…)`) already sit at `l ⊔ li`, so no user-visible
level changes. CIC's `l` alone (indices do not raise the level) would only
matter for a large-indexed family, such as an `HList` over a list of codes.
None exists, and getting `l` alone would mean taking the index out of the
code. Revisit only if such a family appears.

---

## 2. Introduction

```
Γ ⊢ a : S        Γ ⊢ cs : DVec^{l⊔li}(n[a/x]; i. IWf(…)(c[a/x]))
------------------------------------------------------------------
Γ ⊢ sup_i^{l,li}(…; a; cs) : IWf(…)(o[a/x])
```

The rule is fully annotated, so it synthesizes. A value at a *convertible*
index spelling `m ≈ o[a]` checks by conversion; nothing is cast. That is
route 2b's §9 rule 1 ("pass it bare"), which now holds by typing, not by
generator discipline.

---

## 3. `dnth`: derived, not primitive

`nth`'s schema (`wf-former-design.md` §3) fixes the element type. For a
dependent tuple the family changes along the recursion (`F[inr j/i]`), and
a motive cannot quantify over families. Instead the family stays fixed
over the full length `n`, and the motive quantifies over an **embedding**
`e : Fin k̂ → Fin n`:

```
dnth^l(n; i. F; cs; i) :=
  elim_Nat( k̂. Π(e : Fin k̂ → Fin n). Π(cs : DVec(k̂; j. F[e j/i])). Π(i' : Fin k̂). F[e i'/i]
          ; λe cs i'. elim_Empty(…; i')
          ; k̂ r. λe cs i'. case i' of { inl _ ⇒ fst cs
                                       | inr j ⇒ r (λj. e (inr j)) (snd cs) j }
          ; n) (λi. i) cs i
```

The result type `F[(λi. i) i/i]` is `F[i/i]` by β, so the ih's type
(§4) holds only up to that β, not syntactically. Likewise the step's
recursive call is at family `F[(λj. e (inr j)) j/i]`, which is
`F[e (inr j)/i]` up to β. `nth` needs no β there, and it was already the
hardest lemma of `Wf`'s metatheory: the Coq formalization had to state it
through reductions, because `nth`'s recursive call is its reduct only up to
substitution lemmas (its M15a, `V_nth`). `dnth` adds a β step to each
of those. This is a cost for the metatheory, not a reason to change the
rule, and it is the first thing the formalization's IWf relation probe
checks. Checked in Coq with
`F` fixed over `Fin n` (§11): at a literal arity and a **neutral** tuple
it reduces to the projections, `dnth(3; F; cs; inr (inl ⟨⟩)) ≡ fst (snd cs)`,
by `reflexivity`. That property is what made `nth` usable for `Wf`'s ih.
The eliminator's typing and β rules materialize this schema, as `elim_Wf`'s
do `nth`'s.

---

## 4. Elimination and β

```
Γ ⊢ t : IWf(…)(m)
Γ, j : I, z : IWf(…)(j) ⊢ M : Type @ l'
Γ, a : S,
   cs : DVec(n[a/x]; i. IWf(…)(c[a/x])),
   ih : Π(i : Fin n[a/x]). M[c[a/x]/j, dnth(…; cs; i)/z]
 ⊢ s : M[o[a/x]/j, sup_i(a; cs)/z]
---------------------------------------------------------------
Γ ⊢ elim_IWf^{l,li,l'}(…; j z. M; a cs ih. s; m; t) : M[m/j, t/z]
```

β fires on the constructor, **whatever the index**, open subterms
included:

```
elim_IWf(…; j z. M; a cs ih. s; _; sup_i(_; a₀; cs₀))
  ⇝ s[ a₀, cs₀, λ(i : Fin n[a₀/x]). elim_IWf(…; c[a₀/x, i/i]; dnth(…; cs₀; i)) ]
```

This is `elim_Wf`'s rule with the index threaded through. The difference
from route 2b is the point of the round. **There is no form B.**
Every constructor computes on open data, including a computed result
index (`App(n, m, f, a) : Term(S(plus(n, m)))`). §8.4 of
`docs/inductive-fording-lowering.md`, "a declaration all of whose recursive
constructors are form B admits no induction over open data at all", does
not arise. Checked in Coq (§11): `size (app n m f a) ≡ S (size f + size a)`
with `n, m, f, a` all variables, by `reflexivity`.

---

## 5. Conversion and neutrality

- `IWf` is **positive, no η**, like `Wf`. Type conversion is structural:
  every component convertible, index included, and levels equal.
- `sup_i` values compare by shape and children. The children compare at
  `DVec` type, where the reductions hand them to Σ-η and `Unit`-irrelevance
  componentwise. **Value equality is equality of the visible data** (route
  2b's §11 bar) because there is no other data. No irrelevance arm is
  involved.
- `elim_IWf` is neutral on a neutral scrutinee. `DVec` is neutral at a
  neutral length, and two neutral `DVec` types compare by length and family,
  under one binder.

The `conv.rs` footprint is one type-reduction case (`DVec`), structural
type-compare cases for `DVec` and `IWf`, and one neutral-elim case. That is
`Wf`'s footprint, and there is no strip, cast or irrelevance arm.

---

## 6. Codes and the meta layer

```
TmDVec { level, len: term, fam: code ⟨i⟩ }            El(TmDVec k i.f) ⇝ DVec(k; i. El f)
TmIWf  { levels, idx: code, shape: code,
         arity ⟨x⟩, out ⟨x⟩, child ⟨x,i⟩, at: term }   El(TmIWf …) ⇝ IWf(El idx; …)(at)
sup_i, elim_IWf                                        term formers, mirroring §2 and §4
```

Code-recursor bill, with `Wf`'s landing as the yardstick (8 branches):
`ty_dvec`/`tm_dvec`, `ty_iwf`/`tm_iwf`, `tm_sup_i`, `tm_elim_iwf`. That is
**6 branches**, or 4 if `Vec`/`Wf` are re-expressed and their branches
retired (§10). `tm_elim_iwf`'s telescope is `tm_elim_wf`'s plus the index
binder `j`. The five parallel transcriptions apply as always. It is the
expensive part, as it was for `Wf`.

---

## 7. What this retires, and what stays

- **Route 2b's generator** (`crates/elab/src/forded.rs`): the skeleton,
  `μ`, the transp chain of §7, the eliminator's form B, and §9's cast rule
  and its structural walker. Form A's motive inversion (casing the
  motive's index by the index type's eliminator) **stays**, relocated. It
  is how a `match` at a specific index gets definitional inversion (§8.3).
  Its `transp`-based recovery of child indices (`child_projection`) goes,
  since the child indices are now fields.
- **`transp`, and with it the strip rule, is removed** (decided
  2026-09-30). `sEq`/`srefl`/`sEmpty`/`elim_sEmpty` and their irrelevance
  laws **stay** as strict propositions. That is the part the Coq
  formalization checked (M10a), and it has no UIP. After this round:
  - `sEq` has no eliminator;
  - `sEq` is a type inhabited exactly when its endpoints convert, with one
    proof up to conversion;
  - that is all the nominal tag uses (`Tag_D = sEq(Nat; k; k)`,
    `docs/inductive-tier0-lowering.md` §3.3);
  - `absurd`'s no-confusion goes through `J` (`inductive.rs`), not
    `transp`.

  Fording is `transp`'s only producer. Every other mention is a generic
  term walk: display, module image, emission walk, `lgg`, the oracle's
  head search.

  Keeping `transp` restricted to strict motives (`sEq`, `sEmpty`) would buy
  `sEq`'s symmetry, transitivity and congruence, and `sEq(0; 1) → sEmpty`.
  Nothing needs these. Re-adding them is additive and cheap: GCST allow
  that elimination without K, and it needs no strip, because at a strict
  motive every equation is irrelevance. The removal therefore costs
  nothing that cannot be had back. It deletes `Conv::strip`, `transp`'s
  reduction step and its code-recursor branch (`Branches` has 56 today,
  `term.rs:800`; 55 before §6's additions). It is a revision of `docs/sprop-design.md`'s frozen
  §4–§5, recorded there.
- **`issues/seq-strip-type-former-negatives.md`** and the head-only strip
  gap become moot: nothing generated contains a cast.

UIP after this round: the known derivation needs `sEq → Id`, which is
`transp` at a relevant motive, and that is gone. `IWf`'s eliminator is
Dybjer's, not Streicher's K, the same position as Coq's and Agda's
inductive families without K. Index inversion (§8.3) uses the index type's
own eliminator. No model check has been done; §12 records it as an open
item.

---

## 8. The generator

### 8.1 Lowering

A surface family `inductive D<ā> : (m : I) → Type { C_k(fields) : D(e_k), … }`
lowers to one `IWf`:

- **Shape** `S`: tier 0's sum of per-constructor payload records, tag
  discipline unchanged. The difference from route 2b is that
  **child-index fields are stored**, as ordinary fields of the payload.
- **Arity** `n`: case on the tag, giving each constructor's literal count
  of recursive fields.
- **Output index** `o`: case on the tag, giving the constructor's written
  result index `e_k` over its fields.
- **Child index** `c`: case on the tag, then on the literal position,
  giving the child's written index (any expression over the fields).
- **Constructors**: `sup_i` with literal `DVec` tuples.

### 8.2 What stops being rejected

Route 2b's restrictions F1–F3 exist because fording *recomputes* a child's
index from the child (`μ`), and a label cannot mention its children. Here
the index is *typed*, not recomputed, so each goes:

| route 2b rejection | example | under `IWf` |
|---|---|---|
| F1: child at a non-variable index | `Node(l: T(0), r: T(n)) : T(S n)` | `c(a, 0) := 0`. Fine |
| F2: two children at one index | `Node(n, l: T(n), r: T(n)) : T(plus(n,n))` | `c(a, _) := n`. Fine, no coherence predicate (checked, §11) |
| F3: payload mentions a child index | `Cons(n, x: Fin(n), xs: V(n)) : V(S n)` | `n` is stored, so `x : Fin(n)` is an ordinary dependent field (checked, §11) |

The index-type restrictions (`inductive.rs:1091`: unparameterized,
unindexed, no container field, at least two constructors) were there for
fording's fingerprint and form A's `Case` tree. The *family* needs none of
them. `I` may be any type, multi-index families are a Σ-index, and
parameterized index types are fine. Only inversion (§8.3) needs structure
on `I`.

### 8.3 `match`

The eliminator's motive ranges over *all* indices. A `match` whose scrutinee
is at a variable index needs nothing more. At a **specific** index `D(e)`:

- **Constructor-headed `e`**: the motive cases on the index by `I`'s
  eliminator, which is fording's form A device and route 1's. The arms at
  impossible indices reduce to `Unit`, and each possible arm gets its
  payload with β definitional. Checked in Coq for
  `vhead : V(S n) → A` (§11), whose β holds by `reflexivity` on
  `vcons n x y xs` with everything open.
- **Non-invertible `e`** (such as `plus(n, m)`): **index abstraction, no
  equations.** This is Coq's `match … in D j return …` inference. Abstract
  `e` out of the expected type to get the motive `j z. M[j/e]`. If that
  motive is well-typed, each arm is checked at its constructor's index
  `o[a]` and β stays definitional. It covers every `match` whose result
  type depends on the index only through `e`. It is a small elaborator
  addition, and it ships with `IWf`.

Decided 2026-09-30: the two tiers above ship with `IWf`. A third tier is
the documented next step, built when an example needs it and not before.

- **Equations, unification without K.** Some arms need a fact abstraction
  cannot give, such as `n = n'` from `S n = S n'`. For these, generalize
  the motive over the index with an `Id(I; j; e)` premise, instantiated at
  the call site with `refl`, and solve the equations in the arm. This is
  the Equations-plugin design (Cockx et al.): solution, injectivity and
  conflict steps, with no-confusion derived for the index type. The
  arm's `J` meets the call site's `refl` whenever the scrutinee is a
  constructor application, so β still computes there.

  The one step that needs K is deleting a reflexive equation `x = x`. It is
  allowed only at index types with decidable equality, justified by a K
  lemma generated from Hedberg's theorem for that type. UIP stays local and
  provable, never assumed. Fording never needed any of this, because its
  stored proof played the equation's role.

### 8.4 Value equality, no-confusion, injectivity

- **Value equality** is equality of the shape and the children, with no
  proof component (§5). The route-2 hazard (`Id`-stored proofs) cannot arise:
  nothing is stored.
- **Cross-spelling** is typing: `IWf(…)(m)` and `IWf(…)(m')` are one type
  when `m ≈ m'`.
- **Disjointness and injectivity** are the shape's (tier 0 §6), verbatim.

The one thing route 2b's §11 said a user *cannot* get, `Id(I; μ s; m)` from
a family value, is now available: for `t : IWf(…)(m)`,
`Id(I; o[shape t]; m)` holds by `elim_IWf` at motive
`j z. Id(I; o[shape z]; j)`, whose arm is `refl`.

---

## 9. Metatheory (ch. 07) obligation — **done**, checked in Coq (M17)

This is expected to be a restriction of `W`'s and an extension of `Wf`'s,
by the same three moves `wf-former-design.md` §8 recorded:

- `DVec`, like `Vec`, should cost **no LR case**: its reducts are `Unit`
  and `Σ`, and at a neutral length it is a neutral type. It owes the
  neutral-type congruence laws, with one more binder than `Vec`'s.
- `IWf`'s type relation is `Wf`'s plus a term relation at `I` for the
  index. Its term relation is `NfEqWf`'s finite Σ-spine. The typing of
  `sup_i` at a convertible index goes through conversion, which the
  relation reads through typed reduction like every other former.
- The index lemma for `dnth` replaces `Wf`'s one for `nth`.

**No negative premise, no conversion premise in reduction, no strip.**
This is the property the whole round is for. `transp`'s metatheory stalled
on exactly those (`issues/sprop-strip-normalization-open.md`,
`../Lean/delam/M10_DESIGN.md` S1–S5). The Coq formalization would take `IWf`
as its own milestone, after `W`/`Wf`, which it does not have yet.

**Outcome (2026-10-21).** All three predictions hold, mechanized rather
than on paper, in heather-coq's M17 (`M17_DESIGN.md`; no admits, no
axioms; the frozen §1–§6 unchanged):
- `DVec` has no LR case: `LogRel/Def.v`'s relation gains no constructor
  for it. At a canonical length it is `Unit`'s or `Σ`'s case by typed
  weak-head expansion, at a neutral length a neutral type, built by
  `LR_dvec_nat` (`Validity/DVec.v`) over a semantic family `DFam`
  (the family moves along the recursion, unlike `Vec`'s). It owes the one
  neutral-type law with a binder, `gne_ty_dvec`, and the algorithm's
  `actne_dvec`.
- `IWf`'s relation is `Wf`'s plus the index: `LRiwf` over `IWfRel`,
  `IWfNf` and the spine `DVecISp` (`LogRel/Def.v`), with the index an
  index of the three families, not a parameter. A `sup_i` at a
  convertible index goes through conversion: `IWfNf` relates `o[a]` to the
  type's index at `I`. Validity: `V_iwf`, `V_supi` (`Validity/IWf.v`),
  `V_elimIWf`, `V_elimIWf_supi` (`Validity/IWfElim.v`).
- `dnth`'s index lemma replaces `nth`'s: `V_dnth`
  (`Validity/DVecNth.v`). The ih's type being `F[i]` only up to β (§3)
  added one validity step to `V_nth`'s composition, and a Unit-η step at
  the `inl` arm.
The fundamental theorem, decidable conversion, type checking and the
consequences (canonicity, preservation) hold with these cases at layers
D and M, and the codes and the six recursor branches at every layer but
V (M17c).

---

## 10. Relation to `Vec`/`Wf`

`Vec = DVec(_; _. T)` and `Wf = IWf` at `I = Unit`, as **translations**,
not as conversions. Unit-η absorbs the index, but `elim_Wf`'s ih goes through
`nth` and `elim_IWf`'s through `dnth` (§3). The two agree at a canonical
arity and are distinct stuck `elim_Nat`s at a neutral one. At a neutral
length `Vec` and `DVec` are distinct neutral types (§1.1), and `Wf` and
`IWf` are distinct formers, so they never convert. Three options, in
increasing churn:

1. Keep all four formers. `IWf` is only used for families.
2. Re-express `Vec`/`Wf` as abbreviations. The kernel keeps `Conv::vec_ty`'s
   fast path keyed on the constant family, and 4 code branches retire.
3. Retire `Vec`/`Wf` outright. The simplest kernel, and the largest migration.

Decided 2026-10-13: **1 now, 2 as the target.** Under option 1 the
elaborator picks one spelling per declaration (unindexed data is `Wf`,
indexed data is `IWf`), so the non-conversions above never meet. Option 2
moves after the generator lands. It adds the index components to every
unindexed type and term, so it may well be slower at first; that is
accepted, to be won back by optimization work as `Wf`'s was, not a reason
to stay at option 1. Option 2 makes `Vec`/`Wf` the *only* spellings of
their instances, which is what §1.1 requires. Retiring `transp` needs none
of this: `Wf` never used it, and its only producer is fording (§7).

---

## 11. Evidence

A Coq probe (`../Lean/delam/probes/IwfProbe.v`, 2026-09-30) checks the
following, closed under the global context. It should become a kernel
acceptance test once the former exists.

- `dnth` stated with a fixed `F` over `Fin n` and an embedding-indexed
  motive (§3); `dnth` of a neutral 3-tuple is its projections, by
  `reflexivity`.
- `Tm` with `Lit : Tm(1)` and `App(n, m, f, a) : Tm(S(n+m))`, lowered as
  §8.1. `size (app n m f a) ≡ S (size f + size a)` on open data, by
  `reflexivity`.
- F2's `node2 : T(n) → T(n) → T(n + n)` and F3's
  `vcons(n, x : Fin n, y, xs : V(n)) : V(S n)` type-check as lowered.
- `vhead (vcons n x y xs) ≡ y` on open data, by the index-casing motive.

The probe stores children as functions (Coq's positivity checker rejects
the `DVec`-nested occurrence). The claims above do not depend on that
representation. The one that does (value equality through Σ/Unit η) is
`Wf`'s, unchanged.

---

## 12. Open questions

Decided 2026-09-30:
- the level is `l ⊔ li` (§1.2);
- `transp` is removed (§7);
- `match` is tiers 1–2 now and tier 3 on demand (§8.3).

Decided 2026-10-13: §1–§6 are frozen; `Vec`/`Wf` are option 1 now, option 2
as the target (§10). The items below are the generator's and do not change
a typing or reduction rule.

1. **Inversion at a parameterized or container index type.** The motive's
   index case is `I`'s eliminator, so it is as available as that
   eliminator is. It is probably free, but the generator's form A device
   was written against the restricted index types. Checked at `List a` (heather-coq
   `probes/IwfLowering.v`, `IwfLowering3.v`), including form A into the
   family itself (`All p (x :: xs) → All p xs`), which needs `I`'s and the
   shapes' codes and a convoy in the motive when it reads the index's
   child; a container index type is not checked.
2. **Mutual families.** They come as one family indexed by `Σ(tag). I_tag`,
   as for tier 0. Checked in heather-coq's rules
   (`probes/IwfLowering.v`, `IwfLowering2.v`; `issues/iwf-former.md`,
   2026-10-20 and 2026-10-21): at a common `I_tag` nothing new; at a
   tag-dependent one the `I_tag` need codes and the motive's case on
   `snd j` is a convoy on `fst j`.
3. ~~**No-UIP, checked.**~~ Paper argument done, 2026-09-30:
   `docs/no-uip-model.md`. The model is the groupoid model, with `Ty 0` as
   sets and bijections. The strict propositions are unions of connected
   components of the context, proved there. DeLaM's globals and `□` are
   interpreted in stages, argued rather than checked. `UIP₀` at `Ty 0` is
   empty. The same model validates `transp` at strict motives and refutes
   a relevant `transp`. Review of §4 of that document is still owed. It
   does not gate the freeze (2026-10-13): removing `transp` only removes a
   rule, and `elim_IWf` is Dybjer's eliminator, which Coq and Agda have
   without K. The review backs the claim that Heather does not prove UIP,
   not the soundness of this rule set, which the ch. 07 round (§9) checks.
4. **Migration of existing 2b declarations.** The acceptance suites
   (`indexed_route_2b*.rs`) re-run against the new lowering. Their
   form-B negatives should flip to positives.

## 13. Sequencing

1. ~~This document reviewed and the rule set frozen.~~ Done 2026-10-13
   for §1–§6. `docs/no-uip-model.md` §4's review was decoupled from this
   step (§12.3) and is still owed.
2. ~~`DVec` lands, with `dnth`'s materialization and the neutral-tuple
   projection test.~~ Done 2026-10-17 (`crates/kernel/tests/dvec.rs`).
   `Type::DVec`, its two reductions in both reducers, its neutral
   congruence, and `term::dnth` transcribed from heather-coq's `tmDNth`.
   Gated to layers p and m (`Tc::computing_layer`) until step 4.
3. ~~`IWf`/`sup_i`/`elim_IWf`, with β on open data at a computed index as
   the headline test, and value equality with no irrelevance arm.~~ Done
   2026-10-20 (`crates/kernel/tests/iwf.rs`). The three in both reducers,
   typing, both conversion domains, with the neutral `elim_IWf` arm typed
   as heather-coq's (scrutinees, motive level, motive, step; not the
   signature, the index or the ih types). F1–F3 are hand-built and
   type-checked there. Gated to layers p and m until step 4.
4. The rec.rs round (§6).
5. ~~The ch. 07 round (§9).~~ Done in heather-coq's M17, checked by Coq
   (2026-10-16; recorded 2026-10-21): §9's three predictions hold, with
   the lemma names there.
6. The generator: route 2b's declarations re-lowered, F1–F3 lifted,
   `match` tiers 1–2, and `transp` removed from the kernel.
