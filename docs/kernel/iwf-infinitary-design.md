# Indexed families with infinitary premises: the `IWf` route on `W`

Status: **landed** (2026-10-25), no-confusion and `cong` up to conversion
added the same day (§13); the scheme was written before the code (2026-10-24), for
`issues/indexed-infinitary-families.md`, option 2 ("a tier-2 lowering for
indexed families: `W` plus an index well-formedness predicate, no kernel
change"). §12 records what writing the code changed.

The customer is the heather-coq port (`docs/heather-coq-port-assessment.md`
§4.2): a logical relation in logrel-coq's style is an indexed family whose
constructors have premises quantified over Kripke worlds,
`∀ ρ : Δ ≤ Γ, LR Δ (dom[ρ])`. Heather covers each half on its own:

- the `IWf` route (`docs/kernel/iwf-former-design.md` §8, `iwf_family.rs`) lowers
  any indexed family whose children are **plain**, `l: D(e)`;
- tier 2 (`docs/inductives/inductive-tier2-w-lowering.md`, `infinitary.rs`) lowers an
  **unindexed** declaration with a recursive **function** field
  `k: (y: A) -> D`, at most one recursive field per constructor.

This document lowers the combination, `k: (y: A) -> D(e)` in an indexed
family, with any number of recursive fields per constructor. It reuses the
`IWf` route's surface (the declaration form, the classifier, the shape, the
`match` motive with its inversion, the recursion guard with its index
rebinding) and replaces only what the kernel's `IWf` cannot say: its
children are a `DVec`, so finitely many.

Conventions are tier 2's: `⟦T⟧` the lowering, `⌜T⌝` a code, `Γ` the ambient
context. The hazard class is the tiers': a bug here produces a checked
theorem about a type the user did not write, and review of this document is
what catches that.

---

## 1. Scope

An indexed declaration is on **this route** when it is on the `IWf` route
(not route 1) and some constructor has a recursive function field

```
k: (y: A) -> D<p̄>(e)
```

with `D<p̄>` the uniform occurrence, `A` not mentioning `D`, and `e` any
expression at the index type over the constructor's stored fields **and
`y`**. A plain child `l: D<p̄>(e)` is the `Unit`-domain case of the same
thing. `A` may mention the type parameters and the stored fields.

What this round lowers:

1. any number of recursive fields per constructor, each plain or function,
   in any order among the payload fields;
2. one arrow per function field (`A -> D(e)`, not `A -> B -> D(e)`); a
   curried premise is written over a record or `Σ` domain;
3. every function domain has a code, and all of them live at one level `lp`
   (tier 2 §1.5, for the same reason: every branch of the positions' case
   tree is a code at `Ty lp`);
4. no container field.

The index type is whatever the `IWf` route accepts. Nothing about the index
type changes here.

A declaration with no function field stays on the kernel's `IWf`, byte for
byte. An unindexed declaration with a function field stays on tier 2, byte
for byte. This route adds a case; it moves neither boundary.

## 2. Why neither existing encoding

`IWf` stores the children as `DVec(n; i. IWf(…)(c[a, i]))`, a Σ-chain of
literal length: η holds, nothing has to be rebuilt, and nothing is stored
about the index because the constructor is *at* its index. There is no
`DVec` of a function's worth of children, so a function field has no
`IWf` spelling.

Tier 2's `W` takes one children function `f : Π(p : P a). W₀`. A
constructor with one recursive field bridges back to it by Π-η and Unit-η
(tier 2 §2.3); a leaf needs the `canon` equation and a `J` (§2.1); several
recursive fields need η for sums (§2.2), and tier 2 refuses them. A logical
relation's Π case has two infinitary premises and its neutral case none, so
both obstacles are in the customer's first constructor.

And `W` has no index.

## 3. The two equations

The encoding is tier 2's, with two facts carried in the predicate instead
of one:

```
W₀           = W(x : S). P(x)
⟦D<ā>(m)⟧    = Σ(t : W₀). El(ok t m)
ok(sup(a; f), j) = Σ(e : Id(I; o(a); j)). REST          the index equation, then
REST = Id(Π(p : P a). W₀; f₀; f)                        no recursive field
     | CH(a, f)                                         one
     | Σ(k̄ : K̄(a)). Σ(q : Id(Π(p : P a). W₀; ρ(k̄); f)). CH(a, f)    two or more
```

- **The index equation** is what "indexed" means on `W`: the tree carries
  no index, so the value carries a proof that its root constructor's
  written result index is the one in the type. A constructor stores
  `refl(o(a))`; a `match` transports along it with `J`, whose motive
  generalizes over the right endpoint, so each arm is checked at its own
  constructor's index, exactly as an `IWf` arm is.
- **The children equation** is present exactly when the constructor's
  recursive fields are not one (zero, or two or more). A `match` arm is
  typed at the user's constructor form, whose children function is the
  one the constructor builds from its fields, `λp. case p of inj_t y ⇒
  k_t y`; relating that to the scrutinee's abstract `f` is η for sums (or,
  at zero fields, the initial-object η), which the kernel does not have. So
  the value carries the equation and a `match` transports along it with
  `J`. At zero fields its left endpoint is tier 2's closed `f₀`, and this
  is tier 2's leaf equation verbatim. At one field it is not needed: Π-η
  and Unit-η make the rebuilt function convertible with `f` (tier 2 §2.3).

  At two or more, the left endpoint has to be **independent of `f`**, which
  is why the fields are stored a second time, as `k̄ : K̄(a)` (`K_t = Π(y :
  A_t). W₀`, or `W₀` for a plain field), and the equation is `Id(ρ(k̄); f)`
  with `ρ(k̄) = λp. case p of inj_t y ⇒ k_t y`. The obvious alternative,
  `Id(ρ(f); f)` with `ρ(f)` rebuilt from `f`'s own restrictions, does not
  transport: `J` generalizes `f` to a `g`, and the predicate at `sup(a; g)`
  asks for `Id(ρ(g); g)`, which a proof of `Id(ρ(f); g)` is not. With `k̄`
  stored, generalizing `f` touches only the `q` slot (and `CH`, below), and
  the base case `g := ρ(k̄)` reduces each child back to `k_t y` by β and ι.
- **`CH(a, f)`** is the product, over the constructor's recursive fields in
  order, of each child's own `ok` at its written index:

  ```
  CH_t = Π(y : A_t). El(ok(f(inj_t y), c_t(a, y)))     function field
  CH_t = El(ok(f(inj_t ⟨⟩), c_t(a)))                   plain field
  CH   = CH_1 × … × CH_n,  right-nested, Unit at n = 0
  ```

So `ok` is tier 2's `canon` with two changes: it is a function of the index
as well as the tree (its motive is `Π(j : I). Ty lk`, not `Ty lw`), and its
equation at a constructor is the conjunction of the index's and the
children's, not only the leaf's.

## 4. The positions and the child index

`P` is a case tree over the shape into codes at `Ty lp`, branch `k`:

```
P_k(v) = ⌜Empty^lp⌝              no recursive field
       = ⌜A_1⌝[v]                one (⌜Unit^lp⌝ if plain)
       = ⌜A_1 + (A_2 + … + A_n)⌝[v]    n ≥ 2, right-nested
```

with each `A_t` elaborated over the branch value's projections, the
`IWf` route's `decl_payload_cx`. `inj_t` is the identity at `n = 1` and the
`inl`/`inr` path into the right-nested sum otherwise.

The child index `c_t(v, y)` is the field's written index elaborated in the
same context with `y` bound at `A_t`. Unlike the `IWf` route's
`c(x, i)`, which is part of the kernel signature, here it is only ever
written inside `ok`'s branch, where the branch value and `y` are in scope:
nothing outside the predicate reads it.

## 5. The type

```
W₀       = W^{ls,lp}(x : S). P(x)                       at lw = ls ⊔ lp
ok(t)    = elim_W^{ls,lp,·}(x:S. P; _. Π(j : I). Ty lk; a f ih. OK; t)
⟦D⟧(m)   = Σ^{lw,lk}(t : W₀). El^{lk}(ok(t) m)           at lk = li ⊔ lw
```

`OK` is tier 2's convoy: a case on `a` with `f` and `ih` generalized into
the case motive (tier 1 §6's lesson; `P a` is stuck on the variable `a`).
Branch `k`, value `v`, `f'`, `ih' : Π(p : P v). Π(j : I). Ty lk`:

```
λf'. λih'. λj. ⌜Σ(e : Id(I; o_k(v); j)). REST⌝      REST as in §3
CH_t = ⌜Π(y : A_t). El(ih' (inj_t y) c_t(v, y))⌝     (function)
     = ih' (inj_t ⟨⟩) c_t(v)                          (plain)
```

`CH` reads the children's facts through the step's `ih'`, which is `ok` at
the subtrees `f'(inj_t y)`: the facts are about the tree's own children, not
about `k̄`, because only the tree's children have an `ok` to recurse to.

Levels: the `Id` at `I` is at `li`, the children equation at `lw`, a child's
fact at `lk`, and every `Σ` code joins them, so each branch is exactly a
code at `lk = li ⊔ lw`. The predicate's motive is `Π(j : I). Ty lk`.

Reading back. `IwfFam` gains a second form: the kernel's `IWf(sig)(m)`, or
this `Σ(t : W₀). El(app(ok_t; m))`, recognized by its second component
being an application of an `elim_W` over the bound tree to an index. The
index is the application's argument; the declaration is found by the
shape's nominal tag, through the `IWf` route's shape registry. Tier 2's
reader (`WParts::read`) requires the second component to be the `elim_W`
itself (or the named `D#canon`), so neither encoding is mistaken for the
other.

## 6. Constructors

```
⟦C_k(b̄, r̄)⟧ at D(m) = ⟨ sup(ℓ_k; kids), ⟨refl(o_k), REST⟩ ⟩
n = 0:  kids = f₀,                  REST = refl(f₀)
n = 1:  kids = λy. fst(r_1 y),      REST = λy. snd(r_1 y)     (λu. fst(r_1), snd(r_1) if plain)
n ≥ 2:  k_t  = λy. fst(r_t y),      kids = ρ(k̄),
        REST = ⟨k̄, ⟨refl(ρ(k̄)), ⟨λy. snd(r_1 y), …⟩⟩⟩
```

The label is the `IWf` route's, from the payload arguments. Each child is
checked at the family instance its written index names, `D(c_t(b̄, y))`
under `y : A_t` for a function field. The index check is the `IWf`
route's: the written result index at the arguments converts with the
expected family's.

`ok(sup(ℓ_k; kids), m)` reduces by `elim_W` β and the case on the
injection to exactly the per-constructor Σ of §5, whose children's facts
mention `kids(inj_t y)`, which reduces (β, the case on an injection, β) to
`fst(r_t y)`, the child's own tree; so each `λy. snd(r_t y)` checks.

## 7. `match`

The `IWf` route's `match` interface, unchanged: a motive `M` over
`(Γ, j : I, z : D(j))`, each arm checked at `M(o_k(v), z_k)` with `z_k` the
arm's constructor form, inversion and abstraction by
`iwf_match_motive` (`docs/kernel/iwf-former-design.md` §8.3) as they are. Only the
eliminator behind it differs:

```
match s = elim_W(x:S. P; w. M'(w); a f ih. STEP; fst s) m (snd s)
M'(w)   = Π(j : I). Π(c : El(ok w j)). M(j, ⟨w, c⟩)
STEP    = (case a of Q) f ih
Q(v)    = Π(f' : Π(p : P v). W₀). Π(ih' : Π(p : P v). M'(f' p)). M'(sup(v; f'))
```

Branch `k`, value `v`: `λf'. λih'. λj. λc. BODY`, with `c` at the §5 Σ:

```
BODY  = J(I; o_k(v); j' e'. Π(r : R(f')). M(j', ⟨sup(v; f'), ⟨e', r⟩⟩);
          B₁; j; fst c) (snd c)
B₁    = λcs. ARM                                                   n = 1
B₁    = λq. J(Π(p : P v). W₀; f₀; g q'. M(o_k(v), ⟨sup(v; g), ⟨refl, q'⟩⟩); ARM; f'; q)    n = 0
B₁    = λr. J(Π(p : P v). W₀; ρ(k̄); g q.
              Π(cs : CH(g)). Π(ih'' : Π(p : P v). M'(g p)).
                M(o_k(v), ⟨sup(v; g), ⟨refl, ⟨k̄, ⟨q, cs⟩⟩⟩⟩);
              λcs. λih''. ARM; f'; q) cs ih'            n ≥ 2, r = ⟨k̄, ⟨q, cs⟩⟩
```

`R(f')` is the Σ after the index equation. At two or more fields the
second `J` generalizes the facts `CH(g)` and the ih along with `g`, since
both are stated about the tree's children; at the base case `g := ρ(k̄)`
each `ρ(k̄)(inj_t y)` reduces to `k_t y`, so there the facts and the ih are
about the stored children, which is what the arm's aliases are built from.
It is applied to the scrutinee's `cs` and the step's `ih'` at the end.

`ARM` is the user's arm, checked at the base case's value, with the binder
aliases:

| field | `n = 1`: alias, its ih | `n ≥ 2`: alias, its ih |
|---|---|---|
| payload | tier 0's projection out of `v` | the same |
| plain `t` | `⟨f'(⟨⟩), cs⟩`, `ih' ⟨⟩ c_t cs` | `⟨k_t, cs_t⟩`, `ih'' (inj_t ⟨⟩) c_t cs_t` |
| function `t` | `λy. ⟨f' y, cs y⟩`, `λy. ih' y c_t(y) (cs y)` | `λy. ⟨k_t y, cs_t y⟩`, `λy. ih'' (inj_t y) c_t(y) (cs_t y)` |

The arm's goal is the user's constructor form up to conversion: §6's
`kids` at these aliases is `ρ(k̄)` (β, `fst` of a pair, Π-η), its `k̄` is
`k̄` (Π-η), its facts are `cs` (β, `snd` of a pair, Π-η, Σ-η), and both
equations are `refl`. On a constructor value both stored equations are
`refl`, so both `J`s compute and **β is definitional**, with the payload
and the children open.

## 8. Recursion

The guard is the `IWf` route's (`GuardKind::Wf`, with `rebind` for the
index parameter), with tier 2's function children added
(`FnChildIh`): a self-call whose decreasing argument is `k(e)`, for `k` a
function field's alias, at **any** `e`, lowers to the function child's ih
applied to `e`. The index parameter must then be passed as the child's
written index at that argument, `c_t(v, e)`: the rebind entry of a function
child is a term under one binder, instantiated at the call's `e` and
compared by term, as a plain child's entry is.

## 9. What the stored equations cost

Values carry proofs, which the `IWf` route was designed to avoid
(`docs/kernel/iwf-former-design.md`, opening). The cost is bounded:

- Every value the elaborator builds carries `refl` in both slots, and every
  value a `match` reads back carries the scrutinee's own proofs, so two
  spellings of one value never differ in the proof component.
- Value equality *across* constructions needs nothing, because nothing in
  this round compares derivations: a logical relation is eliminated, not
  compared, and that is the use the issue names. A future need to compare
  two derivations meets UIP at `I` (Hedberg at a decidable index, which
  every index type the route accepts today has) and funext at function
  children, which tier 2 already documents (§12 item 8 there).
- No axiom: `Ψ` stays empty, as it did for tier 2 and `Acc`.

## 10. Not in this round

Curried function fields (`(y: A) -> (z: B) -> D(e)`); container fields;
`inj` at a recursive field (tier 2 §9's reason, unchanged); no-confusion
(`absurd`, payload `inj`) on this route (this said the `IWf` route's own
`absurd` reads `Supi`; in fact neither form had `absurd` or `inj` until §13,
which adds them to both); generated-definition naming of
`ok` (tier 2 §13's lever, to pull when a measured profile asks); native and
certificate generators, which keep refusing.

## 11. Acceptance

`crates/elab/tests/iwf_infinitary.rs`, every term kernel-checked, against
`docs/testing-generated-terms.md`'s axes:

1. A family with a leaf, a plain child, a function child and a constructor
   with two function children declares and constructs, at open payloads
   (axis 2).
2. Closed computation through a function child by `refl` (axis 1, literal).
3. β on open data: a `match` on `C(b̄, k)` with everything open reduces to
   the arm, by `refl` (axis 1, neutral data inside a constructor).
4. Induction at a neutral derivation with a dependent motive, through both
   function children and at the rebound index (axis 3).
5. A neutral scrutinee does not compute (axis 4).
6. Negative controls: a child built at the wrong index, a self-call at a
   non-subtree, a self-call at the wrong index, a curried field, a domain
   with no code.
7. Index inversion: a `match` at a constructor-headed index omits the arms
   whose constructors cannot reach it.
8. A logical-relation miniature: types `Base | Arr(A, B)`, a relation
   indexed by the type with the arrow case's premise quantified over
   arguments, and a lemma proved by induction over it.

## 12. As landed

The code is `crates/elab/src/iwf_w.rs`: the signature (`IwSig`, `iw_sig`),
constructors (`build_iw_ctor`), `match` (`iw_match`, `iw_arm`) and the arm
context with its guard (`iw_arm_cx`). The `IWf` route's family handle
carries either form (`iwf_family.rs`, `FamForm::{IWf, W}`), so the surface
around it (the motive, inversion, the arm environment) is shared;
`IndexedRoute::IwfW` names the route. What writing it changed or settled:

1. **Function domains are read back after the signature exists.** While
   `iw_sig` builds `P`, the domains are elaborated from their spelling with
   the type parameters bound (`field_scope_cx`'s type variables). At a
   constructor or a `match` the family is known only by its type, which has
   no arguments to bind a parameter to, so the domains are split out of
   `P(label)` instead (`split_positions`): the type itself for one recursive
   field, the right-nested sum's summands for more. A child's written index
   is still elaborated under `y` from its spelling.
2. **The kernel caught two mis-scoped annotations, and only under a motive
   that reads the scrutinee.** The pair inside a `match` motive's value
   (§7) annotated `REST` one binder short, and `J₂`'s motive passed `r`
   and `g` where `g` and `q` belonged. A motive that ignores `z` (every
   `fn` returning `Nat`) discards that value before the kernel checks its
   annotations, so `size`, `cp` and every β test passed with both bugs in.
   Induction (`cp_size`), the logical relation's lemma, and an inverted
   motive (which cases on `z`'s index) each exposed them. For generated
   `match` terms this is a fifth axis beside
   `docs/testing-generated-terms.md`'s four: a motive that depends on the
   scrutinee.
3. **Mutual groups carry function fields.** §1 left them out by omission;
   the group's family is an ordinary indexed declaration, so the only change
   is in `mutual_family.rs`, which now rewrites `(y: A) -> E(e)`'s codomain
   to the family occurrence when `A` names no member. Under a member
   constructor, the guard's rebind for a function child is the member's own
   index, read under `y` (as `docs/inductives/mutual-inductive-design.md` §5 reads a
   plain child's).
4. **A self-call through `k(e)` at an index other than the child's**
   (`bad(add(2, m), k(3))` with `k(3) : Tr(add(3, m))`) is refused by the
   guard ("must pass `n` unchanged"), before typing would refuse it: the
   rebind entry is compared by term, as §8 planned.
5. **Inferred `cong` does not see through rebuilt children.** A value is a
   pair, and a function applied to a constructor built from another
   function's result reduces to `⟨fst X, snd X⟩` with annotations spelled
   over the arm's variables. That is convertible to `X` but not
   syntactically equal, and anti-unification is syntactic. Proofs state the
   congruence's endpoints instead (the suite's `succ_eq`, `add_eq`):
   [[cong-inference-through-iwf-w-children]].
6. **Acceptance as run.** All of §11 holds, with three adjustments. The
   two-children constructor is a function child beside a plain one
   (`Two`, `VC`), which takes the same `k̄` path as two function children.
   Index inversion needs every constructor's output index
   constructor-headed, as on the `IWf` route, so it is tested on its own
   family (`Tv`); `Tr`'s `Two : Tr(n)` reaches every index. And "a domain
   with no code" cannot be written from the surface: every type the
   surface elaborates to has a code (`code.rs` refuses only kernel-internal
   formers), so the check in `iw_sig` stays as a guard with no test that
   reaches it. Beyond §11: an open element type as payload and domain, and
   mutual groups (unindexed, and an indexed member whose function child
   varies its index).
7. No-confusion on this route stays out (§10):
   [[iwf-w-no-confusion]]. Landed in §13, with item 5's `cong`.

## 13. No-confusion and `cong` up to conversion

The round after §12, for [[iwf-w-no-confusion]] and
[[cong-inference-through-iwf-w-children]].

**No-confusion on both forms.** `absurd` and `inj` had no case for an
indexed family on either route: `build_absurd`/`build_inj` read a tier-0
declaration's `Sup`, and an `IWf`-route family (kernel `IWf` or the `W`
form) fell through to "not an inductive". `crates/elab/src/iwf_confusion.rs`
adds the tier-0 §6 scheme for a family handle, so both forms share it:

- *Reading a side.* Each side is whnf'd and read as a constructor: the label
  of a `Supi` (kernel form) or of the `Sup` under the pair's `fst` (`W`
  form), then the label's injection path picks the constructor and its
  payload tuple. A neutral side is refused, as on tier 0.
- *The constant-motive function.* `absurd` transports along `p : l = r`
  with motive `y ↦ El⁰(tag_i(y))`, where `tag_i` is an `elim_IWf` (kernel
  form) or an `elim_W` on `fst y` (`W` form) whose step ignores its
  children and answers `Unit` at constructor `i`, `Empty` elsewhere; the
  case is `⋆` and the result is eliminated with `elim_Empty`. `inj` at
  payload field `k` uses the same eliminator with a step that projects field
  `k` of the label (the field's own default elsewhere), and answers
  `Id(A_k; a_k; b_k)`. Neither motive ever inspects the index, so both are
  correct at any index and need no inversion.
- *What stays out.* `inj` at a recursive field is refused with tier 2 §9's
  reason: the children are the tree's subtrees, not fields of the label. A
  dependent payload field (`A_k` mentioning earlier fields) is accepted when
  its type at both sides converts. The reported endpoints are the written
  tuple's components, so a wrong `inj` claim fails as a mismatch at the
  surface rather than as an unspellable kernel term.

**`cong` up to conversion.** §12 item 5's failure was anti-unification
being syntactic: the reduct of `f(C(…, g(x)))` mentions `⟨fst X, snd X⟩`
and arm-spelled annotations where the other side has `X`. The fix is general
(`lgg.rs`, `lgg_body_up_to_conversion`), not route-specific: when the
syntactic and the whnf'd attempts both fail, a third pass anti-unifies the
whnf'd sides again, but at the outermost binder level (no bound variables
of the term in scope) it may also put the hole at any pair of subterms that
convert to the equation's endpoints `s` and `t`. Conversion runs in `Γ`,
where the sides are scoped: the walk never weakens a side into `Γ, z`, only
the pieces it keeps, so no large reduct is shifted or strengthened
(strengthening them was the first attempt's cost, weakening them whole the
second's).
The generalized body is accepted only if `λz.body` kernel-checks at
`?f`'s type; otherwise the second attempt's mismatch is reported, so a goal
that is not a congruence keeps its old diagnostic.

Costs, as shapes: the third pass converts at most each subterm pair the
syntactic walk reaches against two fixed terms, and runs only when the
first two fail. The second attempt's whnf of the goal reads the reduct's
constructor off the value (`readback.rs`, `Readback::term_head`) instead of
respelling it by substitution through the `J` transports (§7), so its cost
is one evaluation plus one substitution per field closure, not one copy of
the transports' motives per reduction step; plain `cong` closes the `k̄`
arms too ([[elab-whnf-family-transport-cost]]). `rewrite` is unchanged: it
finds an occurrence by head, which a rebuilt child's reduct lacks.
